import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegBgC1Pair
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderLowBaseH2VB

/-!
# Fixed-background order-zero coefficient pairs

This module estimates the order-zero correction caused by replacing the
frozen DeTurck background with a fixed smooth background.  Exact Palatini
factorization is performed before the `H¹` estimate, so the state difference is
measured only in `H²` and no fourth state derivative occurs.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [BoundarylessManifold I M] in
private theorem jetSub
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (m : ℕ)
    (A B : SmoothCcTensor g r s) :
    lowJetSq (I := I) (M := M) g m (A - B) ≤
      2 * (lowJetSq (I := I) (M := M) g m A +
        lowJetSq (I := I) (M := M) g m B) := by
  rw [sub_eq_add_neg]
  refine (jetAdd (I := I) (M := M) g m A (-B)).trans ?_
  have hneg := jetSmul (I := I) (M := M) g m (-1 : ℝ) B
  rw [neg_one_smul, neg_one_sq, one_mul] at hneg
  rw [hneg]

private theorem domH1
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g 0 s) :
    lowJetSq (I := I) (M := M) g 1
        (domDomCongrSection (I := I) g σ S) =
      lowJetSq (I := I) (M := M) g 1 S := by
  unfold lowJetSq
  apply Finset.sum_congr rfl
  intro q _
  rw [SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun x =>
    riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
      (I := I) (M := M) g σ S q x

set_option linter.unusedVariables false in
private theorem appH21
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (p r c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r),
        lowJetSq (I := I) (M := M) g 1
            (appCcRS (I := I) (M := M) g p r c Φ W) ≤
          C * lowJetSq (I := I) (M := M) g 2 Φ *
            lowJetSq (I := I) (M := M) g 1 W := by
  obtain ⟨C₀, hC₀, happ⟩ :=
    appRS_h2_h1_h1 (I := I) (M := M) hDim g p r c
  refine ⟨C₀ ^ 2, sq_nonneg _, ?_⟩
  intro Φ W
  let A : ℝ := Real.sqrt (lowJetSq (I := I) (M := M) g 2 Φ)
  let B : ℝ := Real.sqrt (lowJetSq (I := I) (M := M) g 1 W)
  have hΦ0 := jetNn (I := I) (M := M) g Φ
  have hW0 := jetNn (I := I) (M := M) g W
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hAsq : A ^ 2 = lowJetSq (I := I) (M := M) g 2 Φ := by
    simpa only [A] using Real.sq_sqrt hΦ0
  have hBsq : B ^ 2 = lowJetSq (I := I) (M := M) g 1 W := by
    simpa only [B] using Real.sq_sqrt hW0
  have hnorm := happ Φ W A B hA hB
    (by simpa only [lowJetSq, Nat.reduceAdd] using le_of_eq hAsq.symm)
    (by simpa only [lowJetSq, Nat.reduceAdd] using le_of_eq hBsq.symm)
  have hsq := pow_le_pow_left₀
    (norm_nonneg (⟨appCcRS (I := I) (M := M) g p r c Φ W⟩ :
      SmoothCcTensorH1 g p c)) hnorm 2
  rw [h1_jet_sq (I := I) (M := M) g p c
    (appCcRS (I := I) (M := M) g p r c Φ W)] at hsq
  calc
    lowJetSq (I := I) (M := M) g 1
        (appCcRS (I := I) (M := M) g p r c Φ W) ≤
      (C₀ * A * B) ^ 2 := by
        simpa only [lowJetSq, Finset.sum_range_succ,
          Finset.sum_range_zero, zero_add, Nat.reduceAdd,
          iteratedCovGrad_zero, iteratedCovGrad_succ] using hsq
    _ = C₀ ^ 2 * lowJetSq (I := I) (M := M) g 2 Φ *
        lowJetSq (I := I) (M := M) g 1 W := by
      rw [mul_pow, mul_pow, hAsq, hBsq]

set_option linter.unusedVariables false in
private theorem appH12
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (p r c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r),
        lowJetSq (I := I) (M := M) g 1
            (appCcRS (I := I) (M := M) g p r c Φ W) ≤
          C * lowJetSq (I := I) (M := M) g 1 Φ *
            lowJetSq (I := I) (M := M) g 2 W := by
  obtain ⟨C₀, hC₀, happ⟩ :=
    appRS_h1_h2_h1 (I := I) (M := M) hDim g p r c
  refine ⟨C₀ ^ 2, sq_nonneg _, ?_⟩
  intro Φ W
  let A : ℝ := Real.sqrt (lowJetSq (I := I) (M := M) g 1 Φ)
  let B : ℝ := Real.sqrt (lowJetSq (I := I) (M := M) g 2 W)
  have hΦ0 := jetNn (I := I) (M := M) g Φ
  have hW0 := jetNn (I := I) (M := M) g W
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hAsq : A ^ 2 = lowJetSq (I := I) (M := M) g 1 Φ := by
    simpa only [A] using Real.sq_sqrt hΦ0
  have hBsq : B ^ 2 = lowJetSq (I := I) (M := M) g 2 W := by
    simpa only [B] using Real.sq_sqrt hW0
  have hnorm := happ Φ W A B hA hB
    (by simpa only [lowJetSq, Nat.reduceAdd] using le_of_eq hAsq.symm)
    (by simpa only [lowJetSq, Nat.reduceAdd] using le_of_eq hBsq.symm)
  have hsq := pow_le_pow_left₀
    (norm_nonneg (⟨appCcRS (I := I) (M := M) g p r c Φ W⟩ :
      SmoothCcTensorH1 g p c)) hnorm 2
  rw [h1_jet_sq (I := I) (M := M) g p c
    (appCcRS (I := I) (M := M) g p r c Φ W)] at hsq
  calc
    lowJetSq (I := I) (M := M) g 1
        (appCcRS (I := I) (M := M) g p r c Φ W) ≤
      (C₀ * A * B) ^ 2 := by
        simpa only [lowJetSq, Finset.sum_range_succ,
          Finset.sum_range_zero, zero_add, Nat.reduceAdd,
          iteratedCovGrad_zero, iteratedCovGrad_succ] using hsq
    _ = C₀ ^ 2 * lowJetSq (I := I) (M := M) g 1 Φ *
        lowJetSq (I := I) (M := M) g 2 W := by
      rw [mul_pow, mul_pow, hAsq, hBsq]

private theorem armPairH1
    (g gT gU : SmoothRiemannianMetric I M) :
    lowJetSq (I := I) (M := M) g 1
        (lieCovArm2 (I := I) (M := M) g gT -
          lieCovArm2 (I := I) (M := M) g gU) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 *
        lowJetSq (I := I) (M := M) g 1
          (connDiffSection (I := I) gT g -
            connDiffSection (I := I) gU g) := by
  let fr : ℝ := Module.finrank ℝ E
  have hper : ∀ q : ℕ,
      ‖iteratedCovGrad (I := I) g 3 4 q
          (lieCovArm2 (I := I) (M := M) g gT -
            lieCovArm2 (I := I) (M := M) g gU)‖ ^ 2 ≤
        fr ^ 2 *
          ‖iteratedCovGrad (I := I) g 1 2 q
            (connDiffSection (I := I) gT g -
              connDiffSection (I := I) gU g)‖ ^ 2 := by
    intro q
    let F : M → ℝ := fun x => fr ^ 2 *
      riemannianFiberNormSq (I := I) (M := M) g 1 (2 + q) x
        ((iteratedCovGrad (I := I) g 1 2 q
          (connDiffSection (I := I) gT g -
            connDiffSection (I := I) gU g)).toSection x)
    have hF : MeasureTheory.Integrable F
        (riemannianVolumeMeasure (I := I) (M := M) g) := by
      dsimp only [F]
      exact (integrable_riemannianFiberNormSq_toSection
        (I := I) (M := M) g 1 (2 + q)
        (iteratedCovGrad (I := I) g 1 2 q
          (connDiffSection (I := I) gT g -
            connDiffSection (I := I) gU g))).const_mul _
    have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
      (I := I) (M := M) g 3 (4 + q)
      (iteratedCovGrad (I := I) g 3 4 q
        (lieCovArm2 (I := I) (M := M) g gT -
          lieCovArm2 (I := I) (M := M) g gU))
      F hF (fun x => by
        simpa only [F, fr] using
          lieCovArm2_sub_l2 (I := I) (M := M) g gT gU q x)
    have hint : (∫ x,
        riemannianFiberNormSq (I := I) (M := M) g 1 (2 + q) x
          ((iteratedCovGrad (I := I) g 1 2 q
            (connDiffSection (I := I) gT g -
              connDiffSection (I := I) gU g)).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
          ‖iteratedCovGrad (I := I) g 1 2 q
            (connDiffSection (I := I) gT g -
              connDiffSection (I := I) gU g)‖ ^ 2 := by
      rw [SmoothCcTensor.norm_def,
        tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
    dsimp only [F] at hsq
    rw [MeasureTheory.integral_const_mul, hint] at hsq
    exact hsq
  unfold lowJetSq
  calc
    ∑ q ∈ Finset.range 2,
        ‖iteratedCovGrad (I := I) g 3 4 q
          (lieCovArm2 (I := I) (M := M) g gT -
            lieCovArm2 (I := I) (M := M) g gU)‖ ^ 2 ≤
      ∑ q ∈ Finset.range 2, fr ^ 2 *
        ‖iteratedCovGrad (I := I) g 1 2 q
          (connDiffSection (I := I) gT g -
            connDiffSection (I := I) gU g)‖ ^ 2 :=
      Finset.sum_le_sum fun q _ => hper q
    _ = fr ^ 2 * ∑ q ∈ Finset.range 2,
        ‖iteratedCovGrad (I := I) g 1 2 q
          (connDiffSection (I := I) gT g -
            connDiffSection (I := I) gU g)‖ ^ 2 := by
      rw [Finset.mul_sum]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
