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

theorem riemannBiContrFib_fiberComponent_g0frame_eq
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n, g₀.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (hpar : ∀ u : TangentSpace I x, ∑ i : Fin n, g₀.inner x (e i) u ^ 2 = g₀.inner x u u)
    (hexp : ∀ u : TangentSpace I x, u = ∑ i : Fin n, g₀.inner x (e i) u • e i)
    (K J : Fin 2 → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x)) n e K J =
      2 * g₁.inner x
        (riemannOp (LeviCivita (I := I) g₁) x (e (J 0))
          (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x (e (K 0))))
          (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x (e (K 1)))))
        (e (J 1)) :=
  sorry

theorem riemannBiContrFib_diff_fiberNormSq_le
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
    Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((show TensorRSSpace 2 2 I x from
            TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x)) -
          (show TensorRSSpace 2 2 I x from
            TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₀ x)))) ≤
      Real.sqrt 2 * ((δ / (1 - δ)) * Cg₀) +
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
      (Cg₀ + (Real.sqrt 2 * ((δ / (1 - δ)) * Cg₀) +
        (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ) ^ 4)) ^ 2 := by
  have hcoeff : 0 < 1 - δ := by linarith
  set A : TensorRSSpace 2 2 I x :=
    (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x)) with hA
  set B : TensorRSSpace 2 2 I x :=
    (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₀ x)) with hB
  have hrfns_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x A :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 2 x A
  have hpoly_nn : 0 ≤ Real.sqrt 2 * ((δ / (1 - δ)) * Cg₀) +
      (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ) ^ 4 := by positivity
  have hbase_sqrt : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x B) ≤ Cg₀ := by
    have hb_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x B :=
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 2 x B
    rw [show Cg₀ = Real.sqrt (Cg₀ ^ 2) from (Real.sqrt_sq hCg₀).symm]
    exact Real.sqrt_le_sqrt hCg₀_bound
  have hdiff := riemannBiContrFib_diff_fiberNormSq_le
    (I := I) (M := M) (x := x) g₀ g₁ S hbil Cg₀ K hCg₀ hK hCg₀_bound hδ_lt hδ_nn hδ hjet
  have htri := sqrt_riemannianFiberNormSq_le_sub_add
    (I := I) (M := M) g₀ 2 2 x A B
  have hsqrt_bound : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x A) ≤
      Cg₀ + (Real.sqrt 2 * ((δ / (1 - δ)) * Cg₀) +
        (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ) ^ 4) := by
    calc Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x A)
        ≤ Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x (A - B)) +
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x B) := htri
      _ ≤ (Real.sqrt 2 * ((δ / (1 - δ)) * Cg₀) +
            (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ) ^ 4) + Cg₀ :=
            add_le_add hdiff hbase_sqrt
      _ = Cg₀ + (Real.sqrt 2 * ((δ / (1 - δ)) * Cg₀) +
            (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ) ^ 4) := by ring
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
  have hcoeff₀ : 0 < 1 - δ₀ := by linarith
  have hsqrt2_nn : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  refine ⟨Real.sqrt 2 * (1 / (1 - δ₀)) * Cg₀ +
      (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ₀) ^ 4, ?_, ?_⟩
  · have hleak_nn : 0 ≤ Real.sqrt 2 * (1 / (1 - δ₀)) * Cg₀ :=
      mul_nonneg (mul_nonneg hsqrt2_nn (by positivity)) hCg₀_nn
    have hpoly_nn : 0 ≤ (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ₀) ^ 4 := by
      positivity
    linarith
  · intro g₁ S hbil δ hδ_le hδ_nn hδ x hjet
    have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
    have hcoeff : 0 < 1 - δ := by linarith
    have hptwise := riemannBiContrFib_fiberNormSq_le_of_metricJet_pointwise
      (I := I) (M := M) (x := x) g₀ g₁ S hbil Cg₀ K hCg₀_nn hK
      (hCg₀_sup x) hδ_lt hδ_nn hδ hjet
    refine hptwise.trans ?_
    have hmono_poly : (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ) ^ 4
        ≤ (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ₀) ^ 4 := by
      have hnum_nn : 0 ≤ (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) := by positivity
      have hden_le : (1 - δ₀) ^ 4 ≤ (1 - δ) ^ 4 := by
        have h1 : (1 - δ₀) ≤ (1 - δ) := by linarith
        exact pow_le_pow_left₀ hcoeff₀.le h1 4
      apply div_le_div_of_nonneg_left hnum_nn (pow_pos hcoeff₀ 4) hden_le
    have hleak_dom : Cg₀ + Real.sqrt 2 * ((δ / (1 - δ)) * Cg₀) ≤
        Real.sqrt 2 * (1 / (1 - δ₀)) * Cg₀ := by
      have hratio : δ / (1 - δ) ≤ δ₀ / (1 - δ₀) := by
        rw [div_le_div_iff₀ hcoeff hcoeff₀]
        nlinarith [hδ_nn, hδ_le, hcoeff, hcoeff₀]
      have hsqrt2_ge1 : (1 : ℝ) ≤ Real.sqrt 2 := by
        rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
        exact Real.sqrt_le_sqrt (by norm_num)
      have hscalar : 1 + Real.sqrt 2 * (δ / (1 - δ)) ≤ Real.sqrt 2 * (1 / (1 - δ₀)) := by
        have hstep1 : Real.sqrt 2 * (δ / (1 - δ)) ≤ Real.sqrt 2 * (δ₀ / (1 - δ₀)) :=
          mul_le_mul_of_nonneg_left hratio hsqrt2_nn
        have hval1 : Real.sqrt 2 * (δ₀ / (1 - δ₀)) = Real.sqrt 2 * δ₀ / (1 - δ₀) := by
          rw [mul_div_assoc]
        have hval2 : Real.sqrt 2 * (1 / (1 - δ₀)) = Real.sqrt 2 / (1 - δ₀) := by
          rw [mul_one_div]
        have hstep2 : 1 + Real.sqrt 2 * (δ₀ / (1 - δ₀)) ≤ Real.sqrt 2 * (1 / (1 - δ₀)) := by
          rw [hval1, hval2, add_div' _ _ _ (ne_of_gt hcoeff₀),
            div_le_div_iff_of_pos_right hcoeff₀]
          nlinarith [hsqrt2_ge1, hδ₀.le, hcoeff₀]
        linarith
      calc Cg₀ + Real.sqrt 2 * ((δ / (1 - δ)) * Cg₀)
          = (1 + Real.sqrt 2 * (δ / (1 - δ))) * Cg₀ := by ring
        _ ≤ (Real.sqrt 2 * (1 / (1 - δ₀))) * Cg₀ :=
            mul_le_mul_of_nonneg_right hscalar hCg₀_nn
        _ = Real.sqrt 2 * (1 / (1 - δ₀)) * Cg₀ := by ring
    have hbase_nn : 0 ≤ Cg₀ + (Real.sqrt 2 * ((δ / (1 - δ)) * Cg₀) +
        (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ) ^ 4) := by
      have h1 : 0 ≤ Real.sqrt 2 * ((δ / (1 - δ)) * Cg₀) :=
        mul_nonneg hsqrt2_nn (mul_nonneg (div_nonneg hδ_nn hcoeff.le) hCg₀_nn)
      have h2 : 0 ≤ (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ) ^ 4 := by positivity
      linarith
    apply pow_le_pow_left₀ hbase_nn (by linarith [hmono_poly, hleak_dom]) 2

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

private lemma slotEndoFib_fiberComponent_slot0
    (g₀ : SmoothRiemannianMetric I M) (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n, g₀.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (K J : Fin 2 → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 0 x Λ)) n e K J =
      g₀.inner x (Λ (e (J 0))) (e (K 0)) * (if K 1 = J 1 then (1 : ℝ) else 0) := by
  have hcomp : fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 0 x Λ)) n e K J =
      Tensor0SBundle.Tensor0SSpace.toModel
        ((slotInsertEndoFib (I := I) (M := M) 2 0 x Λ)
          (coframeS (I := I) (M := M) g₀ x 2 e K))
        (fun k => e (J k)) := by
    unfold fiberNormSqComponent coframeS; rfl
  rw [hcomp, slotInsertEndoFib_apply_eval]
  rw [show (coframeS (I := I) (M := M) g₀ x 2 e K).toModel
        (Function.update (fun k => e (J k)) 0 (Λ (e (J 0))))
      = coframeS (I := I) (M := M) g₀ x 2 e K
        (Function.update (fun k => e (J k)) 0 (Λ (e (J 0)))) from rfl]
  rw [coframeS_apply, Fin.prod_univ_two, Function.update_self,
    Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
  rw [g₀.symm x (e (K 0)) (Λ (e (J 0))), horth (K 1) (J 1)]

private lemma slotEndoFib_fiberComponent_slot1
    (g₀ : SmoothRiemannianMetric I M) (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n, g₀.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (K J : Fin 2 → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 1 x Λ)) n e K J =
      (if K 0 = J 0 then (1 : ℝ) else 0) * g₀.inner x (Λ (e (J 1))) (e (K 1)) := by
  have hcomp : fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 1 x Λ)) n e K J =
      Tensor0SBundle.Tensor0SSpace.toModel
        ((slotInsertEndoFib (I := I) (M := M) 2 1 x Λ)
          (coframeS (I := I) (M := M) g₀ x 2 e K))
        (fun k => e (J k)) := by
    unfold fiberNormSqComponent coframeS; rfl
  rw [hcomp, slotInsertEndoFib_apply_eval]
  rw [show (coframeS (I := I) (M := M) g₀ x 2 e K).toModel
        (Function.update (fun k => e (J k)) 1 (Λ (e (J 1))))
      = coframeS (I := I) (M := M) g₀ x 2 e K
        (Function.update (fun k => e (J k)) 1 (Λ (e (J 1)))) from rfl]
  rw [coframeS_apply, Fin.prod_univ_two, Function.update_self,
    Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)]
  rw [g₀.symm x (e (K 1)) (Λ (e (J 1))), horth (K 0) (J 0)]

private lemma slot01_sqsum_eq (n : ℕ) (F : Fin n → Fin n → ℝ) :
    (∑ K : Fin 2 → Fin n, ∑ J : Fin 2 → Fin n,
      (F (J 0) (K 0) * (if K 1 = J 1 then (1 : ℝ) else 0) +
        (if K 0 = J 0 then (1 : ℝ) else 0) * F (J 1) (K 1)) ^ 2)
      = 2 * (n : ℝ) * (∑ a : Fin n, ∑ b : Fin n, (F a b) ^ 2) +
        2 * (∑ a : Fin n, F a a) ^ 2 := by
  classical
  have hexpand : ∀ g : (Fin 2 → Fin n) → ℝ,
      (∑ p : Fin 2 → Fin n, g p) = ∑ a : Fin n, ∑ b : Fin n, g ![a, b] := by
    intro g
    rw [← (finTwoArrowEquiv (Fin n)).symm.sum_comp g, Fintype.sum_prod_type]; rfl
  have hL : (∑ K : Fin 2 → Fin n, ∑ J : Fin 2 → Fin n,
      (F (J 0) (K 0) * (if K 1 = J 1 then (1 : ℝ) else 0) +
        (if K 0 = J 0 then (1 : ℝ) else 0) * F (J 1) (K 1)) ^ 2)
      = ∑ k0 : Fin n, ∑ k1 : Fin n, ∑ j0 : Fin n, ∑ j1 : Fin n,
          (F j0 k0 * (if k1 = j1 then (1 : ℝ) else 0) +
            (if k0 = j0 then (1 : ℝ) else 0) * F j1 k1) ^ 2 := by
    rw [hexpand]
    refine Finset.sum_congr rfl (fun k0 _ => Finset.sum_congr rfl (fun k1 _ => ?_))
    rw [hexpand]; rfl
  rw [hL]
  have hkey : ∀ k0 k1 j0 j1 : Fin n,
      (F j0 k0 * (if k1 = j1 then (1 : ℝ) else 0) +
        (if k0 = j0 then (1 : ℝ) else 0) * F j1 k1) ^ 2 =
        (F j0 k0) ^ 2 * (if k1 = j1 then (1 : ℝ) else 0) +
          (if k0 = j0 then (1 : ℝ) else 0) * (F j1 k1) ^ 2 +
          2 * ((if k0 = j0 then (1 : ℝ) else 0) * (if k1 = j1 then (1 : ℝ) else 0)) *
            (F j0 k0 * F j1 k1) := by
    intro k0 k1 j0 j1
    by_cases h0 : k0 = j0
    · by_cases h1 : k1 = j1
      · simp only [h0, h1, if_true]; ring
      · simp [h0, h1]
    · by_cases h1 : k1 = j1 <;> simp [h0, h1]
  rw [Finset.sum_congr rfl (fun k0 _ => Finset.sum_congr rfl (fun k1 _ =>
    Finset.sum_congr rfl (fun j0 _ => Finset.sum_congr rfl (fun j1 _ => hkey k0 k1 j0 j1))))]
  have hA : (∑ k0 : Fin n, ∑ k1 : Fin n, ∑ j0 : Fin n, ∑ j1 : Fin n,
        (F j0 k0) ^ 2 * (if k1 = j1 then (1 : ℝ) else 0))
      = (n : ℝ) * ∑ a : Fin n, ∑ b : Fin n, (F a b) ^ 2 := by
    have hstep : ∀ k0 k1 j0 : Fin n,
        (∑ j1 : Fin n, (F j0 k0) ^ 2 * (if k1 = j1 then (1 : ℝ) else 0)) = (F j0 k0) ^ 2 := by
      intro k0 k1 j0
      rw [← Finset.mul_sum, Finset.sum_ite_eq Finset.univ k1 (fun _ => (1 : ℝ))]
      simp
    have hk1 : ∀ k0 : Fin n,
        (∑ k1 : Fin n, ∑ j0 : Fin n, ∑ j1 : Fin n,
          (F j0 k0) ^ 2 * (if k1 = j1 then (1 : ℝ) else 0))
          = (n : ℝ) * ∑ j0 : Fin n, (F j0 k0) ^ 2 := by
      intro k0
      have hk1inner : ∀ k1 : Fin n,
          (∑ j0 : Fin n, ∑ j1 : Fin n,
            (F j0 k0) ^ 2 * (if k1 = j1 then (1 : ℝ) else 0))
            = ∑ j0 : Fin n, (F j0 k0) ^ 2 :=
        fun k1 => Finset.sum_congr rfl (fun j0 _ => hstep k0 k1 j0)
      rw [Finset.sum_congr rfl (fun k1 _ => hk1inner k1), Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Finset.sum_congr rfl (fun k0 _ => hk1 k0), ← Finset.mul_sum]
    refine congrArg (fun t => (n : ℝ) * t) ?_
    rw [Finset.sum_comm]
  have hB : (∑ k0 : Fin n, ∑ k1 : Fin n, ∑ j0 : Fin n, ∑ j1 : Fin n,
        (if k0 = j0 then (1 : ℝ) else 0) * (F j1 k1) ^ 2)
      = (n : ℝ) * ∑ a : Fin n, ∑ b : Fin n, (F a b) ^ 2 := by
    have hj0 : ∀ k0 k1 : Fin n,
        (∑ j0 : Fin n, ∑ j1 : Fin n, (if k0 = j0 then (1 : ℝ) else 0) * (F j1 k1) ^ 2)
          = ∑ j1 : Fin n, (F j1 k1) ^ 2 := by
      intro k0 k1
      have hinner : ∀ j0 : Fin n,
          (∑ j1 : Fin n, (if k0 = j0 then (1 : ℝ) else 0) * (F j1 k1) ^ 2)
            = if k0 = j0 then (∑ j1 : Fin n, (F j1 k1) ^ 2) else 0 := by
        intro j0
        by_cases h : k0 = j0 <;> simp [h]
      rw [Finset.sum_congr rfl (fun j0 _ => hinner j0),
        Finset.sum_ite_eq Finset.univ k0 (fun _ => ∑ j1 : Fin n, (F j1 k1) ^ 2)]
      simp
    rw [Finset.sum_congr rfl (fun k0 _ => Finset.sum_congr rfl (fun k1 _ => hj0 k0 k1))]
    have hk0 : ∀ k0 : Fin n,
        (∑ k1 : Fin n, ∑ j1 : Fin n, (F j1 k1) ^ 2)
          = ∑ a : Fin n, ∑ b : Fin n, (F a b) ^ 2 := by
      intro k0
      rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun k0 _ => hk0 k0), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hC : (∑ k0 : Fin n, ∑ k1 : Fin n, ∑ j0 : Fin n, ∑ j1 : Fin n,
        2 * ((if k0 = j0 then (1 : ℝ) else 0) * (if k1 = j1 then (1 : ℝ) else 0)) *
          (F j0 k0 * F j1 k1))
      = 2 * (∑ a : Fin n, F a a) ^ 2 := by
    have hstep : ∀ k0 k1 : Fin n,
        (∑ j0 : Fin n, ∑ j1 : Fin n,
          2 * ((if k0 = j0 then (1 : ℝ) else 0) * (if k1 = j1 then (1 : ℝ) else 0)) *
            (F j0 k0 * F j1 k1)) = 2 * (F k0 k0 * F k1 k1) := by
      intro k0 k1
      have hj1 : ∀ j0 : Fin n,
          (∑ j1 : Fin n,
            2 * ((if k0 = j0 then (1 : ℝ) else 0) * (if k1 = j1 then (1 : ℝ) else 0)) *
              (F j0 k0 * F j1 k1))
            = if k0 = j0 then (2 * (F j0 k0 * F k1 k1)) else 0 := by
        intro j0
        have hre : ∀ j1 : Fin n,
            2 * ((if k0 = j0 then (1 : ℝ) else 0) * (if k1 = j1 then (1 : ℝ) else 0)) *
              (F j0 k0 * F j1 k1)
              = if k1 = j1 then
                  ((if k0 = j0 then (1 : ℝ) else 0) * (2 * (F j0 k0 * F j1 k1))) else 0 := by
          intro j1
          by_cases h1 : k1 = j1
          · by_cases h0 : k0 = j0 <;> simp only [h0, h1, if_true, if_false] <;> ring
          · simp [h1]
        rw [Finset.sum_congr rfl (fun j1 _ => hre j1),
          Finset.sum_ite_eq Finset.univ k1
            (fun j1 => (if k0 = j0 then (1 : ℝ) else 0) * (2 * (F j0 k0 * F j1 k1)))]
        by_cases h0 : k0 = j0 <;> simp [h0]
      rw [Finset.sum_congr rfl (fun j0 _ => hj1 j0),
        Finset.sum_ite_eq Finset.univ k0 (fun j0 => 2 * (F j0 k0 * F k1 k1))]
      simp
    rw [Finset.sum_congr rfl (fun k0 _ => Finset.sum_congr rfl (fun k1 _ => hstep k0 k1))]
    have hprod : (∑ k0 : Fin n, ∑ k1 : Fin n, 2 * (F k0 k0 * F k1 k1))
        = 2 * ((∑ k0 : Fin n, F k0 k0) * ∑ k1 : Fin n, F k1 k1) := by
      rw [Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k0 _ => ?_)
      rw [Finset.mul_sum]
    rw [hprod, sq]
  simp only [Finset.sum_add_distrib]
  rw [hA, hB, hC]
  ring

private lemma rfns_slot01EndoFib_eq
    (g₀ : SmoothRiemannianMetric I M) (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n, g₀.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (hrepr : ∀ S : TensorRSSpace 2 2 I x,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x S =
        ∑ K : Fin 2 → Fin n, ∑ J : Fin 2 → Fin n,
          fiberNormSqSummand (I := I) (M := M) g₀ x 2 2 S n e K J) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 0 x Λ +
            slotInsertEndoFib (I := I) (M := M) 2 1 x Λ)) =
      2 * (n : ℝ) * (∑ a : Fin n, ∑ b : Fin n, (g₀.inner x (Λ (e a)) (e b)) ^ 2) +
        2 * (∑ a : Fin n, g₀.inner x (Λ (e a)) (e a)) ^ 2 := by
  classical
  have hsplit : (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 0 x Λ +
          slotInsertEndoFib (I := I) (M := M) 2 1 x Λ)) =
      (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 0 x Λ)) +
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 1 x Λ)) := rfl
  rw [riemannianFiberNormSq_eq_sum_componentRS_sq (I := I) (M := M) g₀ x 2 2 e hrepr _, hsplit]
  have hcomp : ∀ (K J : Fin 2 → Fin n),
      (fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
          ((show TensorRSSpace 2 2 I x from
              TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 0 x Λ)) +
            (show TensorRSSpace 2 2 I x from
              TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 1 x Λ))) n e K J) ^ 2 =
        (g₀.inner x (Λ (e (J 0))) (e (K 0)) * (if K 1 = J 1 then (1 : ℝ) else 0) +
          (if K 0 = J 0 then (1 : ℝ) else 0) * g₀.inner x (Λ (e (J 1))) (e (K 1))) ^ 2 := by
    intro K J
    rw [fiberNormSqComponent_add (I := I) (M := M) g₀ x 2 2 _ _ n e K J,
      slotEndoFib_fiberComponent_slot0 (I := I) (M := M) g₀ x Λ e horth K J,
      slotEndoFib_fiberComponent_slot1 (I := I) (M := M) g₀ x Λ e horth K J]
  rw [Finset.sum_congr rfl (fun K _ => Finset.sum_congr rfl (fun J _ => hcomp K J))]
  exact slot01_sqsum_eq n (fun a b => g₀.inner x (Λ (e a)) (e b))

private lemma slotInsertEndoFib_sub (s : ℕ) (k : Fin s) (x : M)
    (A B : TangentSpace I x →L[ℝ] TangentSpace I x) :
    slotInsertEndoFib (I := I) (M := M) s k x A -
        slotInsertEndoFib (I := I) (M := M) s k x B =
      slotInsertEndoFib (I := I) (M := M) s k x (A - B) := by
  have hsub : A - B = A + (-1 : ℝ) • B := by rw [neg_one_smul]; abel
  rw [hsub, slotInsertEndoFib_add_left (I := I) (M := M) s k x A ((-1 : ℝ) • B),
    slotInsertEndoFib_smul_left (I := I) (M := M) s k x (-1 : ℝ) B, neg_one_smul]
  abel

private lemma frobeniusFrame_eq_sum_inner_self
    (g₀ : SmoothRiemannianMetric I M) (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hpar : ∀ v : TangentSpace I x, ∑ i : Fin n, g₀.inner x (e i) v ^ 2 = g₀.inner x v v) :
    (∑ a : Fin n, ∑ b : Fin n, (g₀.inner x (Λ (e a)) (e b)) ^ 2) =
      ∑ a : Fin n, g₀.inner x (Λ (e a)) (Λ (e a)) := by
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← hpar (Λ (e a))]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [g₀.symm x (e b) (Λ (e a))]

private lemma rfns_slot01_leakage_le
    (g₀ : SmoothRiemannianMetric I M) (x : M)
    (B D : TangentSpace I x →L[ℝ] TangentSpace I x) (ρ : ℝ)
    (hop : ∀ v : TangentSpace I x,
      Real.sqrt (g₀.inner x (D v) (D v)) ≤ ρ * Real.sqrt (g₀.inner x v v))
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n, g₀.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (hpar : ∀ v : TangentSpace I x, ∑ i : Fin n, g₀.inner x (e i) v ^ 2 = g₀.inner x v v)
    (hrepr : ∀ S : TensorRSSpace 2 2 I x,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x S =
        ∑ K : Fin 2 → Fin n, ∑ J : Fin 2 → Fin n,
          fiberNormSqSummand (I := I) (M := M) g₀ x 2 2 S n e K J) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 0 x (D.comp B) +
            slotInsertEndoFib (I := I) (M := M) 2 1 x (D.comp B))) ≤
      2 * ρ ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 0 x B +
            slotInsertEndoFib (I := I) (M := M) 2 1 x B)) := by
  classical
  set Fbase : ℝ := ∑ a : Fin n, g₀.inner x (B (e a)) (B (e a)) with hFbase
  set Fleak : ℝ := ∑ a : Fin n, g₀.inner x ((D.comp B) (e a)) ((D.comp B) (e a)) with hFleak
  have hFbase_nn : 0 ≤ Fbase :=
    Finset.sum_nonneg (fun a _ => metric_inner_self_nonneg (I := I) (M := M) g₀ x (B (e a)))
  have hopsq : ∀ v : TangentSpace I x,
      g₀.inner x (D v) (D v) ≤ ρ ^ 2 * g₀.inner x v v := by
    intro v
    have hv_nn : 0 ≤ g₀.inner x v v := metric_inner_self_nonneg (I := I) (M := M) g₀ x v
    have hDv_nn : 0 ≤ g₀.inner x (D v) (D v) :=
      metric_inner_self_nonneg (I := I) (M := M) g₀ x (D v)
    have hsq := hop v
    have h1 := Real.sq_sqrt hv_nn
    have h2 := Real.sq_sqrt hDv_nn
    nlinarith [hsq, h1, h2, Real.sqrt_nonneg (g₀.inner x v v),
      Real.sqrt_nonneg (g₀.inner x (D v) (D v))]
  have hFleak_le : Fleak ≤ ρ ^ 2 * Fbase := by
    rw [hFleak, hFbase, Finset.mul_sum]
    refine Finset.sum_le_sum (fun a _ => ?_)
    have h := hopsq (B (e a))
    simpa using h
  have hbaseeq := rfns_slot01EndoFib_eq (I := I) (M := M) g₀ x B e horth hrepr
  have hleakeq := rfns_slot01EndoFib_eq (I := I) (M := M) g₀ x (D.comp B) e horth hrepr
  have hFbaseeq : (∑ a : Fin n, ∑ b : Fin n, (g₀.inner x (B (e a)) (e b)) ^ 2) = Fbase :=
    frobeniusFrame_eq_sum_inner_self (I := I) (M := M) g₀ x B e hpar
  have hFleakeq : (∑ a : Fin n, ∑ b : Fin n, (g₀.inner x ((D.comp B) (e a)) (e b)) ^ 2) = Fleak :=
    frobeniusFrame_eq_sum_inner_self (I := I) (M := M) g₀ x (D.comp B) e hpar
  rw [hleakeq, hbaseeq, hFleakeq, hFbaseeq]
  set Bform : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun v w => g₀.inner x ((D.comp B) v) w)
      (fun v₁ v₂ w => by simp [map_add])
      (fun c v w => by simp [map_smul])
      (fun v w₁ w₂ => by simp [map_add])
      (fun c v w => by simp [map_smul]) with hBform
  have hBform_apply : ∀ v w : TangentSpace I x,
      Bform v w = g₀.inner x ((D.comp B) v) w := fun v w => rfl
  have htrace : (∑ a : Fin n, g₀.inner x ((D.comp B) (e a)) (e a)) ^ 2 ≤ (n : ℝ) * Fleak := by
    have hbil := DifferentialGeometry.Integral.DivergenceTheorem.bilinForm_trace_sq_le_card_mul_frobenius_sq
      (V := TangentSpace I x) (ι := Fin n) Bform e
    rw [Fintype.card_fin] at hbil
    have hfrob : (∑ a : Fin n, ∑ b : Fin n, (Bform (e a) (e b)) ^ 2) = Fleak := by
      rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by rw [hBform_apply]))]
      rw [hFleakeq]
    have hdiag : (∑ a : Fin n, Bform (e a) (e a)) =
        ∑ a : Fin n, g₀.inner x ((D.comp B) (e a)) (e a) :=
      Finset.sum_congr rfl (fun a _ => by rw [hBform_apply])
    rw [hdiag, hfrob] at hbil
    exact hbil
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hρ2_nn : (0 : ℝ) ≤ ρ ^ 2 := sq_nonneg ρ
  have hleak_main : 2 * (n : ℝ) * Fleak + 2 * Fleak * (n : ℝ) ≤ 2 * ρ ^ 2 * (2 * (n : ℝ) * Fbase) := by
    have h1 : 2 * (n : ℝ) * Fleak ≤ 2 * (n : ℝ) * (ρ ^ 2 * Fbase) :=
      mul_le_mul_of_nonneg_left hFleak_le (by positivity)
    have h2 : 2 * Fleak * (n : ℝ) ≤ 2 * (ρ ^ 2 * Fbase) * (n : ℝ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hFleak_le (by norm_num)) hn_nn
    nlinarith [h1, h2, hn_nn, hρ2_nn, hFbase_nn]
  have htrace_le : (∑ a : Fin n, g₀.inner x ((D.comp B) (e a)) (e a)) ^ 2 ≤ (n : ℝ) * Fleak := htrace
  calc 2 * (n : ℝ) * Fleak +
        2 * (∑ a : Fin n, g₀.inner x ((D.comp B) (e a)) (e a)) ^ 2
      ≤ 2 * (n : ℝ) * Fleak + 2 * ((n : ℝ) * Fleak) := by
        have := htrace_le
        nlinarith [htrace_le, hn_nn, hFbase_nn, hFleak_le, hρ2_nn]
    _ ≤ 2 * ρ ^ 2 * (2 * (n : ℝ) * Fbase) := by
        nlinarith [hleak_main, hn_nn, hFbase_nn, hFleak_le, hρ2_nn]
    _ = 2 * ρ ^ 2 * (2 * (n : ℝ) * Fbase +
          2 * (∑ a : Fin n, g₀.inner x (B (e a)) (e a)) ^ 2) -
          2 * ρ ^ 2 * (2 * (∑ a : Fin n, g₀.inner x (B (e a)) (e a)) ^ 2) := by ring
    _ ≤ 2 * ρ ^ 2 * (2 * (n : ℝ) * Fbase +
          2 * (∑ a : Fin n, g₀.inner x (B (e a)) (e a)) ^ 2) := by
        have hnn : 0 ≤ 2 * ρ ^ 2 * (2 * (∑ a : Fin n, g₀.inner x (B (e a)) (e a)) ^ 2) := by
          positivity
        linarith

def palatiniSummandVec
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) (a v w : TangentSpace I x) :
    TangentSpace I x :=
  (covDerivConnDiff (I := I) g₀ g₁
        (smoothExtensionTangent (I := I) x a)
        (smoothExtensionTangent (I := I) x v)
        (smoothExtensionTangent (I := I) x w) x
      - covDerivConnDiff (I := I) g₀ g₁
        (smoothExtensionTangent (I := I) x v)
        (smoothExtensionTangent (I := I) x a)
        (smoothExtensionTangent (I := I) x w) x)
    + (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
            (smoothExtensionTangent (I := I) x v)
            (smoothExtensionTangent (I := I) x w) x)
          a
        - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
            (smoothExtensionTangent (I := I) x a)
            (smoothExtensionTangent (I := I) x w) x)
          v)

theorem ricciTensor_sub_eq_palatiniSummandVec_basisSum
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    ricciTensor (I := I) g₁ x v w - ricciTensor (I := I) g₀ x v w =
      ∑ i : Fin (Module.finrank ℝ E),
        (Integral.Measure.chartModelBasis E).repr
          (palatiniSummandVec (I := I) g₀ g₁ x ((Integral.Measure.chartModelBasis E) i) v w) i := by
  rw [ricciTensor_sub_eq_connDiff_palatini (I := I) g₀ g₁ x v w]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1
  unfold palatiniSummandVec
  rw [smoothExtensionTangent_eq (I := I) x ((Integral.Measure.chartModelBasis E) i),
    smoothExtensionTangent_eq (I := I) x v]

theorem palatiniSummandVec_eq_riemannOp_sub
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) (a v w : TangentSpace I x) :
    palatiniSummandVec (I := I) g₀ g₁ x a v w =
      riemannOp (LeviCivita (I := I) g₁) x a v w -
        riemannOp (LeviCivita (I := I) g₀) x a v w := by
  classical
  set A := smoothExtensionTangent (I := I) x a with hA
  set V := smoothExtensionTangent (I := I) x v with hV
  set W := smoothExtensionTangent (I := I) x w with hW
  have hA_sm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% A) := smoothExtensionTangent_contMDiff x a
  have hV_sm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V) := smoothExtensionTangent_contMDiff x v
  have hW_sm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W) := smoothExtensionTangent_contMDiff x w
  have hAx : A x = a := smoothExtensionTangent_eq x a
  have hVx : V x = v := smoothExtensionTangent_eq x v
  have hWx : W x = w := smoothExtensionTangent_eq x w
  have htor : (LeviCivita (I := I) g₀).torsion = 0 := LeviCivita_torsion_eq_zero (I := I) g₀
  have hdiff := riemannSec_difference (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
    hA_sm hV_sm hW_sm htor x
  have hr1 : riemannOp (LeviCivita (I := I) g₁) x a v w =
      riemannSec (LeviCivita (I := I) g₁) A V W x := by
    rw [show a = A x from hAx.symm, show v = V x from hVx.symm, show w = W x from hWx.symm,
      riemannOp_apply_smooth (cov := LeviCivita (I := I) g₁) hA_sm hV_sm hW_sm]
  have hr0 : riemannOp (LeviCivita (I := I) g₀) x a v w =
      riemannSec (LeviCivita (I := I) g₀) A V W x := by
    rw [show a = A x from hAx.symm, show v = V x from hVx.symm, show w = W x from hWx.symm,
      riemannOp_apply_smooth (cov := LeviCivita (I := I) g₀) hA_sm hV_sm hW_sm]
  rw [hr1, hr0]
  unfold palatiniSummandVec
  rw [show covDerivConnDiff (I := I) g₀ g₁ A V W x =
      covDerivDiff (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁) A V W x from rfl,
    show covDerivConnDiff (I := I) g₀ g₁ V A W x =
      covDerivDiff (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁) V A W x from rfl]
  rw [show PDE.DeTurck.connDiff (I := I) g₁ g₀ x
        (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁) V W x) a =
      CovariantDerivative.difference (LeviCivita (I := I) g₁) (LeviCivita (I := I) g₀) x
        (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁) V W x) (A x) from by
      rw [hAx]; rfl,
    show PDE.DeTurck.connDiff (I := I) g₁ g₀ x
        (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁) A W x) v =
      CovariantDerivative.difference (LeviCivita (I := I) g₁) (LeviCivita (I := I) g₀) x
        (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁) A W x) (V x) from by
      rw [hVx]; rfl]
  rw [hdiff]
  abel

def riemannOpDiffEndo
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x where
  toFun a := riemannOp (LeviCivita (I := I) g₁) x a v w -
    riemannOp (LeviCivita (I := I) g₀) x a v w
  map_add' a a' := by
    rw [map_add (riemannOp (LeviCivita (I := I) g₁) x),
      ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
      map_add (riemannOp (LeviCivita (I := I) g₀) x),
      ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply]
    abel
  map_smul' c a := by
    rw [map_smul (riemannOp (LeviCivita (I := I) g₁) x),
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
      map_smul (riemannOp (LeviCivita (I := I) g₀) x),
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply]
    rw [smul_sub]
    rfl

@[simp] lemma riemannOpDiffEndo_apply
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) (v w a : TangentSpace I x) :
    riemannOpDiffEndo (I := I) g₀ g₁ x v w a =
      riemannOp (LeviCivita (I := I) g₁) x a v w -
        riemannOp (LeviCivita (I := I) g₀) x a v w := rfl

theorem sqrt_g0_inner_riemannOpDiff_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (x : M)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      ccTensorBilin (I := I) g₀ S b u w = g₁.inner b u w - g₀.inner b u w)
    (K : ℝ) (hK : 0 ≤ K)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ)
    (hδ : gFibreOpBound (I := I) g₀ (ccTensorBilin (I := I) g₀ S) δ)
    (hjet : metricDiffCovJet2Bound (I := I) g₀ S K x) (a v w : TangentSpace I x) :
    Real.sqrt (g₀.inner x
        (riemannOp (LeviCivita (I := I) g₁) x a v w -
          riemannOp (LeviCivita (I := I) g₀) x a v w)
        (riemannOp (LeviCivita (I := I) g₁) x a v w -
          riemannOp (LeviCivita (I := I) g₀) x a v w)) ≤
      (Module.finrank ℝ E : ℝ) * (K + K ^ 2) / (2 * (1 - δ) ^ 3) *
        Real.sqrt (g₀.inner x a a) *
        Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) :=
  sorry

theorem exists_palatiniSummand_linear_opBound
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (x : M)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      ccTensorBilin (I := I) g₀ S b u w = g₁.inner b u w - g₀.inner b u w)
    (K : ℝ) (hK : 0 ≤ K)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ)
    (hδ : gFibreOpBound (I := I) g₀ (ccTensorBilin (I := I) g₀ S) δ)
    (hjet : metricDiffCovJet2Bound (I := I) g₀ S K x) (v w : TangentSpace I x) :
    ∃ G : TangentSpace I x →ₗ[ℝ] TangentSpace I x,
      (∀ a : TangentSpace I x, G a = palatiniSummandVec (I := I) g₀ g₁ x a v w) ∧
      (∀ a : TangentSpace I x,
        Real.sqrt (g₀.inner x (G a) (G a)) ≤
          (Module.finrank ℝ E : ℝ) * (K + K ^ 2) / (2 * (1 - δ) ^ 3) *
            Real.sqrt (g₀.inner x a a) *
            Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)) := by
  refine ⟨riemannOpDiffEndo (I := I) g₀ g₁ x v w, fun a => ?_, ?_⟩
  · rw [riemannOpDiffEndo_apply, palatiniSummandVec_eq_riemannOp_sub]
  · intro a
    rw [riemannOpDiffEndo_apply]
    exact sqrt_g0_inner_riemannOpDiff_le (I := I) (M := M) (x := x)
      g₀ g₁ S hbil K hK hδ_lt hδ_nn hδ hjet a v w

private lemma orthonormalBasis_repr_eq_inner
    (g₀ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (bse : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (e : Fin n → TangentSpace I x) (hbse : ∀ i, bse i = e i)
    (hexp : ∀ u : TangentSpace I x, u = ∑ i : Fin n, g₀.inner x (e i) u • e i)
    (u : TangentSpace I x) (i : Fin n) :
    bse.repr u i = g₀.inner x (e i) u := by
  classical
  conv_lhs => rw [hexp u]
  rw [map_sum, Finsupp.finset_sum_apply]
  rw [Finset.sum_eq_single i]
  · rw [show g₀.inner x (e i) u • e i = g₀.inner x (e i) u • bse i from by rw [hbse]]
    rw [map_smul, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_apply]
    simp
  · intro j _ hj
    rw [show g₀.inner x (e j) u • e j = g₀.inner x (e j) u • bse j from by rw [hbse]]
    rw [map_smul, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_apply]
    simp [hj]
  · intro hi; simp at hi

theorem lowered_raisedRicciDifference_bilin_bound
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (x : M)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      ccTensorBilin (I := I) g₀ S b u w = g₁.inner b u w - g₀.inner b u w)
    (K : ℝ) (hK : 0 ≤ K)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ)
    (hδ : gFibreOpBound (I := I) g₀ (ccTensorBilin (I := I) g₀ S) δ)
    (hjet : metricDiffCovJet2Bound (I := I) g₀ S K x) (v w : TangentSpace I x) :
    |ricciTensor (I := I) g₁ x v w - ricciTensor (I := I) g₀ x v w| ≤
      (Module.finrank ℝ E : ℝ) ^ 2 * (K + K ^ 2) / (2 * (1 - δ) ^ 3) *
        Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) := by
  classical
  have hcoeff : 0 < 1 - δ := by linarith
  obtain ⟨G, hGeq, hGbound⟩ :=
    exists_palatiniSummand_linear_opBound (I := I) (M := M) (x := x)
      g₀ g₁ S hbil K hK hδ_lt hδ_nn hδ hjet v w
  set Cper : ℝ := (Module.finrank ℝ E : ℝ) * (K + K ^ 2) / (2 * (1 - δ) ^ 3) with hCper
  have hCper_nn : 0 ≤ Cper := by
    rw [hCper]
    have : 0 ≤ K + K ^ 2 := by positivity
    positivity
  set Svw : ℝ := Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) with hSvw
  have hSvw_nn : 0 ≤ Svw := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  obtain ⟨nn, ee, bse, hnn, hbse, horth, hpar, hexp, _hrepr⟩ :=
    tangent_orthonormalBasisRS_witness (I := I) (M := M) g₀ 2 2 x
  have hnnE : nn = Module.finrank ℝ E := by rw [hnn]; rfl
  have htrace_type : LinearMap.trace ℝ E G = LinearMap.trace ℝ (TangentSpace I x) G := rfl
  have hchart_eq_trace :
      ∑ i : Fin (Module.finrank ℝ E),
        (Integral.Measure.chartModelBasis E).repr
          (G ((Integral.Measure.chartModelBasis E) i)) i =
        LinearMap.trace ℝ (TangentSpace I x) G := by
    rw [← htrace_type,
      LinearMap.trace_eq_matrix_trace ℝ (Integral.Measure.chartModelBasis E) G, Matrix.trace]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
    rfl
  have hbse_eq_trace :
      ∑ i : Fin nn, bse.repr (G (bse i)) i =
        LinearMap.trace ℝ (TangentSpace I x) G := by
    rw [LinearMap.trace_eq_matrix_trace ℝ bse G, Matrix.trace]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  have htrace_chart : ricciTensor (I := I) g₁ x v w - ricciTensor (I := I) g₀ x v w =
      LinearMap.trace ℝ (TangentSpace I x) G := by
    rw [ricciTensor_sub_eq_palatiniSummandVec_basisSum (I := I) g₀ g₁ x v w, ← hchart_eq_trace]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hGeq ((Integral.Measure.chartModelBasis E) i)]
  have htrace_orth : LinearMap.trace ℝ (TangentSpace I x) G =
      ∑ i : Fin nn, g₀.inner x (ee i) (G (ee i)) := by
    rw [← hbse_eq_trace]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [orthonormalBasis_repr_eq_inner (I := I) (M := M) g₀ x bse ee hbse hexp (G (bse i)) i,
      hbse i]
  rw [htrace_chart, htrace_orth]
  have hterm : ∀ i : Fin nn, |g₀.inner x (ee i) (G (ee i))| ≤ Cper * Svw := by
    intro i
    have hee_unit : g₀.inner x (ee i) (ee i) = 1 := by rw [horth i i]; simp
    have hCS : |g₀.inner x (ee i) (G (ee i))| ≤
        Real.sqrt (g₀.inner x (ee i) (ee i)) * Real.sqrt (g₀.inner x (G (ee i)) (G (ee i))) :=
      abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₀ x (ee i) (G (ee i))
    have hGb := hGbound (ee i)
    rw [hee_unit, Real.sqrt_one, one_mul] at hCS
    refine hCS.trans ?_
    refine hGb.trans ?_
    rw [hee_unit, Real.sqrt_one, mul_one]
    rw [hCper, hSvw]
    ring_nf
    rfl
  calc |∑ i : Fin nn, g₀.inner x (ee i) (G (ee i))|
      ≤ ∑ i : Fin nn, |g₀.inner x (ee i) (G (ee i))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin nn, Cper * Svw := Finset.sum_le_sum (fun i _ => hterm i)
    _ = (nn : ℝ) * (Cper * Svw) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (Module.finrank ℝ E : ℝ) ^ 2 * (K + K ^ 2) / (2 * (1 - δ) ^ 3) *
          Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) := by
        rw [hnnE, hCper, hSvw]
        ring

private lemma g0_inner_eq_g1_inner_invSharpFlat
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) (u w : TangentSpace I x) :
    g₀.inner x u w =
      g₁.inner x u
        (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x w)) := by
  rw [g₁.symm x u (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x w))]
  rw [inverseMetricSharpFib_inner, cotangentToDualLinear_apply, cotangentToDual_g0FlatCLM]
  exact (g₀.symm x w u).symm

private lemma g1_inner_raisedRicciDifference_curvPart
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    g₁.inner x
        (((ricEndoRaisedFib (I := I) g₁ x - ricEndoRaisedFib (I := I) g₀ x) -
            (gInvDiffRaisedEndo (I := I) g₀ g₁ x).comp (ricEndoRaisedFib (I := I) g₀ x)) v) w =
      ricciTensor (I := I) g₁ x v w - ricciTensor (I := I) g₀ x v w := by
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply]
  rw [show g₁.inner x
        (ricEndoRaisedFib (I := I) g₁ x v - ricEndoRaisedFib (I := I) g₀ x v -
          gInvDiffRaisedEndo (I := I) g₀ g₁ x (ricEndoRaisedFib (I := I) g₀ x v)) w =
      g₁.inner x (ricEndoRaisedFib (I := I) g₁ x v) w -
        g₁.inner x (ricEndoRaisedFib (I := I) g₀ x v) w -
        g₁.inner x (gInvDiffRaisedEndo (I := I) g₀ g₁ x (ricEndoRaisedFib (I := I) g₀ x v)) w from by
    rw [map_sub, map_sub, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply]]
  rw [inner_ricEndoRaisedFib (I := I) g₁ x v w,
    inner_g1_gInvDiffRaisedEndo (I := I) g₀ g₁ x (ricEndoRaisedFib (I := I) g₀ x v) w,
    inner_ricEndoRaisedFib (I := I) g₀ x v w]
  ring

private lemma sqrt_g0_inner_raisedRicciDifference_curvPart_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (x : M)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      ccTensorBilin (I := I) g₀ S b u w = g₁.inner b u w - g₀.inner b u w)
    (K : ℝ) (hK : 0 ≤ K)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ)
    (hδ : gFibreOpBound (I := I) g₀ (ccTensorBilin (I := I) g₀ S) δ)
    (hjet : metricDiffCovJet2Bound (I := I) g₀ S K x) (v : TangentSpace I x) :
    Real.sqrt (g₀.inner x
        (((ricEndoRaisedFib (I := I) g₁ x - ricEndoRaisedFib (I := I) g₀ x) -
            (gInvDiffRaisedEndo (I := I) g₀ g₁ x).comp (ricEndoRaisedFib (I := I) g₀ x)) v)
        (((ricEndoRaisedFib (I := I) g₁ x - ricEndoRaisedFib (I := I) g₀ x) -
            (gInvDiffRaisedEndo (I := I) g₀ g₁ x).comp (ricEndoRaisedFib (I := I) g₀ x)) v)) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 * (K + K ^ 2) / (2 * (1 - δ) ^ 4) *
        Real.sqrt (g₀.inner x v v) := by
  classical
  have hcoeff : 0 < 1 - δ := by linarith
  have htie : ∀ (y : M) (u w : TangentSpace I y),
      g₁.inner y u w = g₀.inner y u w + ccTensorBilin (I := I) g₀ S y u w := by
    intro y u w; rw [hbil y u w]; ring
  set Λ : TangentSpace I x →L[ℝ] TangentSpace I x :=
    (ricEndoRaisedFib (I := I) g₁ x - ricEndoRaisedFib (I := I) g₀ x) -
      (gInvDiffRaisedEndo (I := I) g₀ g₁ x).comp (ricEndoRaisedFib (I := I) g₀ x) with hΛ
  set Φ : TangentSpace I x → TangentSpace I x := fun u =>
    inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x u) with hΦ
  set Nv : ℝ := Real.sqrt (g₀.inner x v v) with hNv
  set Nw : ℝ := Real.sqrt (g₀.inner x (Λ v) (Λ v)) with hNw
  have hNv_nn : 0 ≤ Nv := Real.sqrt_nonneg _
  have hNw_nn : 0 ≤ Nw := Real.sqrt_nonneg _
  have hself_nn : 0 ≤ g₀.inner x (Λ v) (Λ v) :=
    metric_inner_self_nonneg (I := I) (M := M) g₀ x (Λ v)
  have hNw_sq : Nw ^ 2 = g₀.inner x (Λ v) (Λ v) := by rw [hNw, Real.sq_sqrt hself_nn]
  have hCb_nn : 0 ≤ (Module.finrank ℝ E : ℝ) ^ 2 * (K + K ^ 2) / (2 * (1 - δ) ^ 3) := by
    have : 0 ≤ K + K ^ 2 := by positivity
    positivity
  have hself_eq : g₀.inner x (Λ v) (Λ v) =
      ricciTensor (I := I) g₁ x v (Φ (Λ v)) - ricciTensor (I := I) g₀ x v (Φ (Λ v)) := by
    rw [g0_inner_eq_g1_inner_invSharpFlat (I := I) g₀ g₁ x (Λ v) (Λ v)]
    exact g1_inner_raisedRicciDifference_curvPart (I := I) g₀ g₁ x v (Φ (Λ v))
  have hbound := lowered_raisedRicciDifference_bilin_bound
    (I := I) (M := M) (x := x) g₀ g₁ S hbil K hK hδ_lt hδ_nn hδ hjet v (Φ (Λ v))
  have hΦle : Real.sqrt (g₀.inner x (Φ (Λ v)) (Φ (Λ v))) ≤ (1 / (1 - δ)) * Nw := by
    have h := sqrt_inner_inverseMetricSharpFib_g0FlatCLM_le
      (I := I) g₀ g₁ (ccTensorBilin (I := I) g₀ S) htie hδ_lt hδ_nn hδ x (Λ v)
    rw [hNw]
    exact h
  have hself_le : g₀.inner x (Λ v) (Λ v) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 * (K + K ^ 2) / (2 * (1 - δ) ^ 3) *
        Nv * ((1 / (1 - δ)) * Nw) := by
    have habs : g₀.inner x (Λ v) (Λ v) ≤
        |ricciTensor (I := I) g₁ x v (Φ (Λ v)) - ricciTensor (I := I) g₀ x v (Φ (Λ v))| := by
      rw [hself_eq]; exact le_abs_self _
    refine habs.trans (hbound.trans ?_)
    have hCb_mul_Nv_nn : 0 ≤ (Module.finrank ℝ E : ℝ) ^ 2 * (K + K ^ 2) / (2 * (1 - δ) ^ 3) * Nv :=
      mul_nonneg hCb_nn hNv_nn
    rw [hNv]
    exact mul_le_mul_of_nonneg_left hΦle hCb_mul_Nv_nn
  have hfinal : Nw * Nw ≤
      ((Module.finrank ℝ E : ℝ) ^ 2 * (K + K ^ 2) / (2 * (1 - δ) ^ 4) * Nv) * Nw := by
    have hne : (1 - δ) ≠ 0 := ne_of_gt hcoeff
    have hrw : (Module.finrank ℝ E : ℝ) ^ 2 * (K + K ^ 2) / (2 * (1 - δ) ^ 3) *
          Nv * ((1 / (1 - δ)) * Nw) =
        ((Module.finrank ℝ E : ℝ) ^ 2 * (K + K ^ 2) / (2 * (1 - δ) ^ 4) * Nv) * Nw := by
      have h4 : (1 - δ) ^ 4 = (1 - δ) ^ 3 * (1 - δ) := by ring
      rw [h4]
      field_simp
    calc Nw * Nw = g₀.inner x (Λ v) (Λ v) := by rw [← hNw_sq, sq]
      _ ≤ (Module.finrank ℝ E : ℝ) ^ 2 * (K + K ^ 2) / (2 * (1 - δ) ^ 3) *
            Nv * ((1 / (1 - δ)) * Nw) := hself_le
      _ = ((Module.finrank ℝ E : ℝ) ^ 2 * (K + K ^ 2) / (2 * (1 - δ) ^ 4) * Nv) * Nw := hrw
  rcases eq_or_lt_of_le hNw_nn with hNw0 | hNwpos
  · rw [hNw] at hNw0 ⊢
    rw [← hNw0]
    have hQ_nn : 0 ≤ (Module.finrank ℝ E : ℝ) ^ 2 * (K + K ^ 2) / (2 * (1 - δ) ^ 4) * Nv := by
      have : 0 ≤ K + K ^ 2 := by positivity
      positivity
    exact hQ_nn
  · rw [hNw]
    have hle := le_of_mul_le_mul_right hfinal hNwpos
    rw [hNw] at hle
    exact hle

private lemma sqrt_rfns_slot01EndoFib_op_le
    (g₀ : SmoothRiemannianMetric I M) (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x) (Q : ℝ) (hQ : 0 ≤ Q)
    (hop : ∀ u : TangentSpace I x,
      Real.sqrt (g₀.inner x (Λ u) (Λ u)) ≤ Q * Real.sqrt (g₀.inner x u u))
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n, g₀.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (hpar : ∀ u : TangentSpace I x, ∑ i : Fin n, g₀.inner x (e i) u ^ 2 = g₀.inner x u u)
    (hrepr : ∀ S : TensorRSSpace 2 2 I x,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x S =
        ∑ K : Fin 2 → Fin n, ∑ J : Fin 2 → Fin n,
          fiberNormSqSummand (I := I) (M := M) g₀ x 2 2 S n e K J) :
    Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 0 x Λ +
            slotInsertEndoFib (I := I) (M := M) 2 1 x Λ))) ≤
      2 * (n : ℝ) * Q := by
  classical
  have hQsq : ∀ u : TangentSpace I x, g₀.inner x (Λ u) (Λ u) ≤ Q ^ 2 * g₀.inner x u u := by
    intro u
    have hu_nn : 0 ≤ g₀.inner x u u := metric_inner_self_nonneg (I := I) (M := M) g₀ x u
    have hΛu_nn : 0 ≤ g₀.inner x (Λ u) (Λ u) :=
      metric_inner_self_nonneg (I := I) (M := M) g₀ x (Λ u)
    have hsq := hop u
    have h1 := Real.sq_sqrt hu_nn
    have h2 := Real.sq_sqrt hΛu_nn
    nlinarith [hsq, h1, h2, Real.sqrt_nonneg (g₀.inner x u u),
      Real.sqrt_nonneg (g₀.inner x (Λ u) (Λ u)), hQ]
  set Fro : ℝ := ∑ a : Fin n, g₀.inner x (Λ (e a)) (Λ (e a)) with hFro
  have hFro_nn : 0 ≤ Fro :=
    Finset.sum_nonneg (fun a _ => metric_inner_self_nonneg (I := I) (M := M) g₀ x (Λ (e a)))
  have hFro_le : Fro ≤ (n : ℝ) * Q ^ 2 := by
    have hstep : ∀ a : Fin n, g₀.inner x (Λ (e a)) (Λ (e a)) ≤ Q ^ 2 := by
      intro a
      have h := hQsq (e a)
      have haa : g₀.inner x (e a) (e a) = 1 := by rw [horth a a]; simp
      rw [haa, mul_one] at h
      exact h
    calc Fro ≤ ∑ _a : Fin n, Q ^ 2 := Finset.sum_le_sum (fun a _ => hstep a)
      _ = (n : ℝ) * Q ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hbaseeq := rfns_slot01EndoFib_eq (I := I) (M := M) g₀ x Λ e horth hrepr
  have hFroeq : (∑ a : Fin n, ∑ b : Fin n, (g₀.inner x (Λ (e a)) (e b)) ^ 2) = Fro :=
    frobeniusFrame_eq_sum_inner_self (I := I) (M := M) g₀ x Λ e hpar
  set Bform : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun u w => g₀.inner x (Λ u) w)
      (fun v₁ v₂ w => by simp [map_add])
      (fun c v w => by simp [map_smul])
      (fun v w₁ w₂ => by simp [map_add])
      (fun c v w => by simp [map_smul]) with hBform
  have hBform_apply : ∀ u w : TangentSpace I x,
      Bform u w = g₀.inner x (Λ u) w := fun u w => rfl
  have htrace_sq : (∑ a : Fin n, g₀.inner x (Λ (e a)) (e a)) ^ 2 ≤ (n : ℝ) * Fro := by
    have hbil := DifferentialGeometry.Integral.DivergenceTheorem.bilinForm_trace_sq_le_card_mul_frobenius_sq
      (V := TangentSpace I x) (ι := Fin n) Bform e
    rw [Fintype.card_fin] at hbil
    have hfrob : (∑ a : Fin n, ∑ b : Fin n, (Bform (e a) (e b)) ^ 2) = Fro := by
      rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by rw [hBform_apply]))]
      rw [hFroeq]
    have hdiag : (∑ a : Fin n, Bform (e a) (e a)) =
        ∑ a : Fin n, g₀.inner x (Λ (e a)) (e a) :=
      Finset.sum_congr rfl (fun a _ => by rw [hBform_apply])
    rw [hdiag, hfrob] at hbil
    exact hbil
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hQ2_nn : (0 : ℝ) ≤ Q ^ 2 := sq_nonneg Q
  have hrfns_le : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 0 x Λ +
          slotInsertEndoFib (I := I) (M := M) 2 1 x Λ)) ≤ (2 * (n : ℝ) * Q) ^ 2 := by
    rw [hbaseeq, hFroeq]
    have hmain : 2 * (n : ℝ) * Fro + 2 * (∑ a : Fin n, g₀.inner x (Λ (e a)) (e a)) ^ 2 ≤
        4 * (n : ℝ) ^ 2 * Q ^ 2 := by
      have ht1 : 2 * (n : ℝ) * Fro ≤ 2 * (n : ℝ) * ((n : ℝ) * Q ^ 2) :=
        mul_le_mul_of_nonneg_left hFro_le (by positivity)
      have ht2 : 2 * (∑ a : Fin n, g₀.inner x (Λ (e a)) (e a)) ^ 2 ≤ 2 * ((n : ℝ) * Fro) :=
        mul_le_mul_of_nonneg_left htrace_sq (by norm_num)
      have ht3 : 2 * ((n : ℝ) * Fro) ≤ 2 * ((n : ℝ) * ((n : ℝ) * Q ^ 2)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hFro_le hn_nn) (by norm_num)
      nlinarith [ht1, ht2, ht3, hn_nn, hQ2_nn, hFro_nn]
    have hpow : (2 * (n : ℝ) * Q) ^ 2 = 4 * (n : ℝ) ^ 2 * Q ^ 2 := by ring
    rw [hpow]
    exact hmain
  refine le_trans (Real.sqrt_le_sqrt hrfns_le) ?_
  rw [Real.sqrt_sq (by positivity)]

theorem raisedRicciDifference_curvPart_slot01_fiberNormSq_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (x : M)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      ccTensorBilin (I := I) g₀ S b u w = g₁.inner b u w - g₀.inner b u w)
    (K : ℝ) (hK : 0 ≤ K)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ)
    (hδ : gFibreOpBound (I := I) g₀ (ccTensorBilin (I := I) g₀ S) δ)
    (hjet : metricDiffCovJet2Bound (I := I) g₀ S K x) :
    Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM
            (slotInsertEndoFib (I := I) (M := M) 2 0 x
                ((ricEndoRaisedFib (I := I) g₁ x - ricEndoRaisedFib (I := I) g₀ x) -
                  (gInvDiffRaisedEndo (I := I) g₀ g₁ x).comp (ricEndoRaisedFib (I := I) g₀ x)) +
              slotInsertEndoFib (I := I) (M := M) 2 1 x
                ((ricEndoRaisedFib (I := I) g₁ x - ricEndoRaisedFib (I := I) g₀ x) -
                  (gInvDiffRaisedEndo (I := I) g₀ g₁ x).comp (ricEndoRaisedFib (I := I) g₀ x))))) ≤
      (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ) ^ 4 := by
  classical
  have hcoeff : 0 < 1 - δ := by linarith
  set Λ : TangentSpace I x →L[ℝ] TangentSpace I x :=
    (ricEndoRaisedFib (I := I) g₁ x - ricEndoRaisedFib (I := I) g₀ x) -
      (gInvDiffRaisedEndo (I := I) g₀ g₁ x).comp (ricEndoRaisedFib (I := I) g₀ x) with hΛ
  set Q : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 * (K + K ^ 2) / (2 * (1 - δ) ^ 4) with hQ
  have hQ_nn : 0 ≤ Q := by
    have : 0 ≤ K + K ^ 2 := by positivity
    rw [hQ]; positivity
  obtain ⟨nn, ee, bse, hnn, hbse, horth, hpar, hexp, hrepr⟩ :=
    tangent_orthonormalBasisRS_witness (I := I) (M := M) g₀ 2 2 x
  have hnnE : (nn : ℝ) = (Module.finrank ℝ E : ℝ) := by rw [hnn]; rfl
  have hop : ∀ u : TangentSpace I x,
      Real.sqrt (g₀.inner x (Λ u) (Λ u)) ≤ Q * Real.sqrt (g₀.inner x u u) := by
    intro u
    have h := sqrt_g0_inner_raisedRicciDifference_curvPart_le
      (I := I) (M := M) (x := x) g₀ g₁ S hbil K hK hδ_lt hδ_nn hδ hjet u
    rw [← hΛ] at h
    rw [hQ]
    exact h
  have hred := sqrt_rfns_slot01EndoFib_op_le
    (I := I) (M := M) g₀ x Λ Q hQ_nn hop ee horth hpar hrepr
  refine hred.trans ?_
  rw [hnnE] at *
  rw [hQ]
  have hne : (1 - δ) ≠ 0 := ne_of_gt hcoeff
  rw [show 2 * (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) ^ 2 * (K + K ^ 2) / (2 * (1 - δ) ^ 4)) =
      (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ) ^ 4 from by
    field_simp]

theorem ricciArmOrder0CurvCoeff_diff_fiberNormSq_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (x : M)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      ccTensorBilin (I := I) g₀ S b u w = g₁.inner b u w - g₀.inner b u w)
    (Cg₀ K : ℝ) (hCg₀ : 0 ≤ Cg₀) (hK : 0 ≤ K)
    (hCg₀_bound : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀).toSection x) ≤ Cg₀ ^ 2)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ)
    (hδ : gFibreOpBound (I := I) g₀ (ccTensorBilin (I := I) g₀ S) δ)
    (hjet : metricDiffCovJet2Bound (I := I) g₀ S K x) :
    Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁).toSection x -
          (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀).toSection x)) ≤
      Real.sqrt 2 * ((δ / (1 - δ)) * Cg₀) +
        (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ) ^ 4 := by
  classical
  have hcoeff : 0 < 1 - δ := by linarith
  let Lleak : TangentSpace I x →L[ℝ] TangentSpace I x :=
    (gInvDiffRaisedEndo (I := I) g₀ g₁ x).comp (ricEndoRaisedFib (I := I) g₀ x)
  let Lcurv : TangentSpace I x →L[ℝ] TangentSpace I x :=
    (ricEndoRaisedFib (I := I) g₁ x - ricEndoRaisedFib (I := I) g₀ x) - Lleak
  let Tcurv : TensorRSSpace 2 2 I x :=
    (show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 0 x Lcurv +
        slotInsertEndoFib (I := I) (M := M) 2 1 x Lcurv))
  let Tleak : TensorRSSpace 2 2 I x :=
    (show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 0 x Lleak +
        slotInsertEndoFib (I := I) (M := M) 2 1 x Lleak))
  have hclm_diff :
      (ricciArmOrder0CurvCoeffFib (I := I) g₁ x - ricciArmOrder0CurvCoeffFib (I := I) g₀ x :
          Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x) =
        (slotInsertEndoFib (I := I) (M := M) 2 0 x Lcurv +
          slotInsertEndoFib (I := I) (M := M) 2 1 x Lcurv) +
          (slotInsertEndoFib (I := I) (M := M) 2 0 x Lleak +
            slotInsertEndoFib (I := I) (M := M) 2 1 x Lleak) := by
    have hLsum : Lcurv + Lleak =
        ricEndoRaisedFib (I := I) g₁ x - ricEndoRaisedFib (I := I) g₀ x := by
      change ((ricEndoRaisedFib (I := I) g₁ x - ricEndoRaisedFib (I := I) g₀ x) - Lleak) + Lleak = _
      abel
    have hrhs : (slotInsertEndoFib (I := I) (M := M) 2 0 x Lcurv +
          slotInsertEndoFib (I := I) (M := M) 2 1 x Lcurv) +
          (slotInsertEndoFib (I := I) (M := M) 2 0 x Lleak +
            slotInsertEndoFib (I := I) (M := M) 2 1 x Lleak) =
        slotInsertEndoFib (I := I) (M := M) 2 0 x (Lcurv + Lleak) +
          slotInsertEndoFib (I := I) (M := M) 2 1 x (Lcurv + Lleak) := by
      rw [slotInsertEndoFib_add_left (I := I) (M := M) 2 0 x Lcurv Lleak,
        slotInsertEndoFib_add_left (I := I) (M := M) 2 1 x Lcurv Lleak]
      abel
    rw [hrhs, hLsum,
      ricciArmOrder0CurvCoeffFib, ricciArmOrder0CurvCoeffFib,
      ricciArmOrder0CurvCoeffFibSlot, ricciArmOrder0CurvCoeffFibSlot,
      ricciArmOrder0CurvCoeffFibSlot, ricciArmOrder0CurvCoeffFibSlot,
      ← slotInsertEndoFib_sub (I := I) (M := M) 2 0 x
        (ricEndoRaisedFib (I := I) g₁ x) (ricEndoRaisedFib (I := I) g₀ x),
      ← slotInsertEndoFib_sub (I := I) (M := M) 2 1 x
        (ricEndoRaisedFib (I := I) g₁ x) (ricEndoRaisedFib (I := I) g₀ x)]
    abel
  have hdiff_eq :
      (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁).toSection x -
        (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀).toSection x = Tcurv + Tleak := by
    rw [ricciArmOrder0CurvCoeff_toSection, ricciArmOrder0CurvCoeff_toSection]
    change (ricciArmOrder0CurvCoeffFib (I := I) g₁ x - ricciArmOrder0CurvCoeffFib (I := I) g₀ x :
        Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x) = _
    exact hclm_diff
  rw [hdiff_eq]
  have htri := sqrt_riemannianFiberNormSq_le_sub_add
    (I := I) (M := M) g₀ 2 2 x (Tcurv + Tleak) Tcurv
  have hcancel : (Tcurv + Tleak) - Tcurv = Tleak := by abel
  rw [hcancel] at htri
  refine htri.trans ?_
  have hcurv_bound : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x Tcurv) ≤
      (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ) ^ 4 :=
    raisedRicciDifference_curvPart_slot01_fiberNormSq_le
      (I := I) (M := M) (x := x) g₀ g₁ S hbil K hK hδ_lt hδ_nn hδ hjet
  have hleak_bound : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x Tleak) ≤
      Real.sqrt 2 * ((δ / (1 - δ)) * Cg₀) := by
    obtain ⟨nn, ee, bse, hnn, hbse, horth, hpar, hexp, hrepr⟩ :=
      tangent_orthonormalBasisRS_witness (I := I) (M := M) g₀ 2 2 x
    have htie : ∀ (y : M) (v w : TangentSpace I y),
        g₁.inner y v w = g₀.inner y v w + ccTensorBilin (I := I) g₀ S y v w := by
      intro y v w; rw [hbil y v w]; ring
    have hopD : ∀ v : TangentSpace I x,
        Real.sqrt (g₀.inner x (gInvDiffRaisedEndo (I := I) g₀ g₁ x v)
            (gInvDiffRaisedEndo (I := I) g₀ g₁ x v)) ≤
          (δ / (1 - δ)) * Real.sqrt (g₀.inner x v v) := fun v =>
      sqrt_inner_gInvDiffRaisedEndo_le (I := I) g₀ g₁
        (ccTensorBilin (I := I) g₀ S) htie hδ_lt hδ_nn hδ x v
    have hleak_rfns := rfns_slot01_leakage_le (I := I) (M := M) g₀ x
      (ricEndoRaisedFib (I := I) g₀ x) (gInvDiffRaisedEndo (I := I) g₀ g₁ x) (δ / (1 - δ))
      hopD ee horth hpar hrepr
    have hbase_le : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM
            (slotInsertEndoFib (I := I) (M := M) 2 0 x (ricEndoRaisedFib (I := I) g₀ x) +
              slotInsertEndoFib (I := I) (M := M) 2 1 x (ricEndoRaisedFib (I := I) g₀ x))) ≤
        Cg₀ ^ 2 := by
      have hBeq : (show TensorRSSpace 2 2 I x from
            TensorRSSpace.ofCLM
              (slotInsertEndoFib (I := I) (M := M) 2 0 x (ricEndoRaisedFib (I := I) g₀ x) +
                slotInsertEndoFib (I := I) (M := M) 2 1 x (ricEndoRaisedFib (I := I) g₀ x))) =
          (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀).toSection x := by
        rw [ricciArmOrder0CurvCoeff_toSection, ricciArmOrder0CurvCoeffFib,
          ricciArmOrder0CurvCoeffFibSlot, ricciArmOrder0CurvCoeffFibSlot]
      rw [hBeq]; exact hCg₀_bound
    have hleak_le_final : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x Tleak ≤
        2 * (δ / (1 - δ)) ^ 2 * Cg₀ ^ 2 := by
      have hcoeff_step := hleak_rfns
      refine hcoeff_step.trans ?_
      have hfac_nn : 0 ≤ 2 * (δ / (1 - δ)) ^ 2 := by positivity
      exact mul_le_mul_of_nonneg_left hbase_le hfac_nn
    have hrhs_sq : (Real.sqrt 2 * ((δ / (1 - δ)) * Cg₀)) ^ 2 = 2 * (δ / (1 - δ)) ^ 2 * Cg₀ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), mul_pow]; ring
    have hrhs_nn : 0 ≤ Real.sqrt 2 * ((δ / (1 - δ)) * Cg₀) := by positivity
    rw [show Real.sqrt 2 * ((δ / (1 - δ)) * Cg₀) =
        Real.sqrt ((Real.sqrt 2 * ((δ / (1 - δ)) * Cg₀)) ^ 2) from (Real.sqrt_sq hrhs_nn).symm]
    apply Real.sqrt_le_sqrt
    rw [hrhs_sq]; exact hleak_le_final
  calc Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x Tleak) +
        Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x Tcurv)
      ≤ Real.sqrt 2 * ((δ / (1 - δ)) * Cg₀) +
          (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ) ^ 4 :=
        add_le_add hleak_bound hcurv_bound

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
      (Cg₀ + (Real.sqrt 2 * ((δ / (1 - δ)) * Cg₀) +
        (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ) ^ 4)) ^ 2 := by
  have hcoeff : 0 < 1 - δ := by linarith
  set A : TensorRSSpace 2 2 I x :=
    (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁).toSection x with hA
  set B : TensorRSSpace 2 2 I x :=
    (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀).toSection x with hB
  have hrfns_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x A :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 2 x A
  have hpoly_nn : 0 ≤ Real.sqrt 2 * ((δ / (1 - δ)) * Cg₀) +
      (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ) ^ 4 := by positivity
  have hbase_sqrt : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x B) ≤ Cg₀ := by
    rw [show Cg₀ = Real.sqrt (Cg₀ ^ 2) from (Real.sqrt_sq hCg₀).symm]
    exact Real.sqrt_le_sqrt hCg₀_bound
  have hdiff := ricciArmOrder0CurvCoeff_diff_fiberNormSq_le
    (I := I) (M := M) (x := x) g₀ g₁ S hbil Cg₀ K hCg₀ hK hCg₀_bound hδ_lt hδ_nn hδ hjet
  have htri := sqrt_riemannianFiberNormSq_le_sub_add
    (I := I) (M := M) g₀ 2 2 x A B
  have hsqrt_bound : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x A) ≤
      Cg₀ + (Real.sqrt 2 * ((δ / (1 - δ)) * Cg₀) +
        (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ) ^ 4) := by
    calc Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x A)
        ≤ Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x (A - B)) +
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x B) := htri
      _ ≤ (Real.sqrt 2 * ((δ / (1 - δ)) * Cg₀) +
            (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ) ^ 4) + Cg₀ :=
            add_le_add hdiff hbase_sqrt
      _ = Cg₀ + (Real.sqrt 2 * ((δ / (1 - δ)) * Cg₀) +
            (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ) ^ 4) := by ring
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
  have hcoeff₀ : 0 < 1 - δ₀ := by linarith
  have hsqrt2_nn : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  refine ⟨Real.sqrt 2 * (1 / (1 - δ₀)) * Cg₀ +
      (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ₀) ^ 4, ?_, ?_⟩
  · have hleak_nn : 0 ≤ Real.sqrt 2 * (1 / (1 - δ₀)) * Cg₀ :=
      mul_nonneg (mul_nonneg hsqrt2_nn (by positivity)) hCg₀_nn
    have hpoly_nn : 0 ≤ (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ₀) ^ 4 := by
      positivity
    linarith
  · intro g₁ S hbil δ hδ_le hδ_nn hδ x hjet
    have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
    have hcoeff : 0 < 1 - δ := by linarith
    have hptwise := ricciArmOrder0CurvCoeff_fiberNormSq_le_of_metricJet_pointwise
      (I := I) (M := M) (x := x) g₀ g₁ S hbil Cg₀ K hCg₀_nn hK
      (hCg₀_sup x) hδ_lt hδ_nn hδ hjet
    refine hptwise.trans ?_
    have hmono_poly : (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ) ^ 4
        ≤ (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ₀) ^ 4 := by
      have hnum_nn : 0 ≤ (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) := by positivity
      have hden_le : (1 - δ₀) ^ 4 ≤ (1 - δ) ^ 4 := by
        have h1 : (1 - δ₀) ≤ (1 - δ) := by linarith
        exact pow_le_pow_left₀ hcoeff₀.le h1 4
      apply div_le_div_of_nonneg_left hnum_nn (pow_pos hcoeff₀ 4) hden_le
    have hleak_dom : Cg₀ + Real.sqrt 2 * ((δ / (1 - δ)) * Cg₀) ≤
        Real.sqrt 2 * (1 / (1 - δ₀)) * Cg₀ := by
      have hratio : δ / (1 - δ) ≤ δ₀ / (1 - δ₀) := by
        rw [div_le_div_iff₀ hcoeff hcoeff₀]
        nlinarith [hδ_nn, hδ_le, hcoeff, hcoeff₀]
      have hsqrt2_ge1 : (1 : ℝ) ≤ Real.sqrt 2 := by
        rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
        exact Real.sqrt_le_sqrt (by norm_num)
      have hscalar : 1 + Real.sqrt 2 * (δ / (1 - δ)) ≤ Real.sqrt 2 * (1 / (1 - δ₀)) := by
        have hstep1 : Real.sqrt 2 * (δ / (1 - δ)) ≤ Real.sqrt 2 * (δ₀ / (1 - δ₀)) :=
          mul_le_mul_of_nonneg_left hratio hsqrt2_nn
        have hval1 : Real.sqrt 2 * (δ₀ / (1 - δ₀)) = Real.sqrt 2 * δ₀ / (1 - δ₀) := by
          rw [mul_div_assoc]
        have hval2 : Real.sqrt 2 * (1 / (1 - δ₀)) = Real.sqrt 2 / (1 - δ₀) := by
          rw [mul_one_div]
        have hstep2 : 1 + Real.sqrt 2 * (δ₀ / (1 - δ₀)) ≤ Real.sqrt 2 * (1 / (1 - δ₀)) := by
          rw [hval1, hval2, add_div' _ _ _ (ne_of_gt hcoeff₀),
            div_le_div_iff_of_pos_right hcoeff₀]
          nlinarith [hsqrt2_ge1, hδ₀.le, hcoeff₀]
        linarith
      calc Cg₀ + Real.sqrt 2 * ((δ / (1 - δ)) * Cg₀)
          = (1 + Real.sqrt 2 * (δ / (1 - δ))) * Cg₀ := by ring
        _ ≤ (Real.sqrt 2 * (1 / (1 - δ₀))) * Cg₀ :=
            mul_le_mul_of_nonneg_right hscalar hCg₀_nn
        _ = Real.sqrt 2 * (1 / (1 - δ₀)) * Cg₀ := by ring
    have hbase_nn : 0 ≤ Cg₀ + (Real.sqrt 2 * ((δ / (1 - δ)) * Cg₀) +
        (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ) ^ 4) := by
      have h1 : 0 ≤ Real.sqrt 2 * ((δ / (1 - δ)) * Cg₀) :=
        mul_nonneg hsqrt2_nn (mul_nonneg (div_nonneg hδ_nn hcoeff.le) hCg₀_nn)
      have h2 : 0 ≤ (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ) ^ 4 := by positivity
      linarith
    apply pow_le_pow_left₀ hbase_nn (by linarith [hmono_poly, hleak_dom]) 2

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
