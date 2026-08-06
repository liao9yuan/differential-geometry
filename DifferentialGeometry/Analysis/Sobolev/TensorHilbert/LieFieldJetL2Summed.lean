import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.ConnDiffJetL2Summed

/-!
# Summed data-weighted jet-L2 bound for the Lie field (REUSE of the connDiff producer)

This file proves the **Lie field** analogue of the connection-difference summed bound in
`ConnDiffJetL2Summed.lean`: a single `R`-independent-top data-weighted jet-L2 bound for the
`(3,4)` field `linearizedRicciConnDiffOrder1KernelField g₀ g₁`.

The construction follows the roadmap of `RemainderCoeffTopSeparated.md` ("Lie — combination of
connDiff"): the Lie field is definitionally the negation of a sum of five slot-permuted /
reindexed copies of `connDiffContrInsertionField g₀ g₁`
(`kernelField_eq_neg_arm_combination`), each copy having the **same** iterated-covariant-gradient
norm as the connDiff field (permutation/reindex are fibrewise isometries).  A triangle inequality
over the five copies (`c3_norm_five_le`) gives the per-order structural bridge
`‖∇^i (Lie …)‖ ≤ 5 · ‖∇^i (connDiff …)‖`, hence `‖∇^i (Lie …)‖² ≤ 25 · ‖∇^i (connDiff …)‖²`.  The
already-landed connDiff summed producer
`connDiffContrInsertionField_realizedFam_jetL2_summed_topSeparated` is then reused as a black box.

Because the bridge multiplies BOTH the connDiff top-split coefficient and the lumped low
coefficient by the same pure combinatorial factor `25` (the `5·`-triangle squared), the resulting
Lie **top-split coefficient `Ktop = 25 · Ktop_connDiff`** stays `(g₀, hδ₀)`-only (`R`-independent),
and `Kc = 25 · Kc_connDiff` follows the accepted house `R`-pattern.

The end shape (both windows land at order `a+2`):
```
∑_{i ≤ a} ‖∇^i (linearizedRicciConnDiffOrder1KernelField g₀ (realizedFam …))‖²
  ≤ Ktop · (∑_{j < a+2} (‖∇^j T‖² + ‖∇^j T'‖²))
  +  Kc  · (1 + ∑_{j < a+2} (‖∇^j T‖² + ‖∇^j T'‖²))
```
This is constituent 4-of-5 of the data-weighted threeArm precursor (R1τ item (2)); see
`UNIF_EXISTENCE_PLAN.md` "Planner acceptance №5" and `RemainderCoeffTopSeparated.md`.  Only
`traceHessian` remains after this.

`slotPermCc`, the seven permutations and `kernelField_eq_neg_arm_combination` are **imported** from
`RicciConnDiffOrder1TameEnvelope.lean`, where they were promoted to public in 2026-08-03 (brick
A1-CUR-1); the local copies this file used to carry were deleted then.  The remaining helpers
(`armOuter_rfns_eq`, `armFull_rfns_eq`, `armOuter_norm_eq`, `armFull_norm_eq`, `c3_norm_five_le`)
are still local copies of `private` originals there; provenance comments mark each.  They use only
public sub-lemmas.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

noncomputable section

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

/-! ### Arm-combination stack — now imported, not copied

The seven permutations (`kOutPerm*`, `kInPerm*`), `slotPermCc` and
`kernelField_eq_neg_arm_combination` used to be copied verbatim into this file because they were
`private` in `RicciConnDiffOrder1TameEnvelope.lean`.  They were promoted to public there
(2026-08-03, brick A1-CUR-1) and the copies deleted; everything below now uses the imported
originals. -/

set_option linter.unusedSectionVars false in
private theorem armOuter_rfns_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (q : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + q) x
        ((iteratedCovGrad (I := I) g₀ 3 4 q
          (appCcRS (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ σ)
            (connDiffContrInsertionField (I := I) g₀ g₁))).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + q) x
        ((iteratedCovGrad (I := I) g₀ 3 4 q
          (connDiffContrInsertionField (I := I) g₀ g₁)).toSection x) := by
  refine rfns_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M) g₀ 3 4 σ
    (connDiffContrInsertionField (I := I) g₀ g₁)
    (appCcRS (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ σ)
      (connDiffContrInsertionField (I := I) g₀ g₁))
    (fun y d => ?_) q x
  have hy : (show Tensor0SBundle.Tensor0SSpace 3 I y →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I y from
      (appCcRS (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ σ)
        (connDiffContrInsertionField (I := I) g₀ g₁)).toSection y) d =
      slotPermCLM (I := I) σ y
        ((show Tensor0SBundle.Tensor0SSpace 3 I y →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I y from
          (connDiffContrInsertionField (I := I) g₀ g₁).toSection y) d) := rfl
  rw [hy, slotPermCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel]

set_option linter.unusedSectionVars false in
private theorem armFull_rfns_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)) (q : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + q) x
        ((iteratedCovGrad (I := I) g₀ 3 4 q
          (reindexCoeffGen (I := I) (M := M) g₀ 3 4
            (appCcRS (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ σ)
              (connDiffContrInsertionField (I := I) g₀ g₁)) ρ)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + q) x
        ((iteratedCovGrad (I := I) g₀ 3 4 q
          (connDiffContrInsertionField (I := I) g₀ g₁)).toSection x) := by
  rw [rfns_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 3 4
    (appCcRS (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ σ)
      (connDiffContrInsertionField (I := I) g₀ g₁)) ρ q x]
  exact armOuter_rfns_eq (I := I) (M := M) g₀ g₁ σ q x

private lemma c3_norm_eq_of_sq_eq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ^ 2 = b ^ 2) : a = b := by
  have hs := congrArg Real.sqrt h
  rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb] at hs

set_option linter.unusedSectionVars false in
private theorem armOuter_norm_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (q : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 3 4 q
        (appCcRS (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ σ)
          (connDiffContrInsertionField (I := I) g₀ g₁))‖ =
      ‖iteratedCovGrad (I := I) g₀ 3 4 q (connDiffContrInsertionField (I := I) g₀ g₁)‖ := by
  refine c3_norm_eq_of_sq_eq (norm_nonneg _) (norm_nonneg _) ?_
  rw [SmoothCcTensor.norm_def, SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 3 (4 + q)
      (iteratedCovGrad (I := I) g₀ 3 4 q
        (appCcRS (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ σ)
          (connDiffContrInsertionField (I := I) g₀ g₁))),
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 3 (4 + q)
      (iteratedCovGrad (I := I) g₀ 3 4 q (connDiffContrInsertionField (I := I) g₀ g₁))]
  have hpt : (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + q) x
        ((iteratedCovGrad (I := I) g₀ 3 4 q
          (appCcRS (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ σ)
            (connDiffContrInsertionField (I := I) g₀ g₁))).toSection x)) =
      (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + q) x
        ((iteratedCovGrad (I := I) g₀ 3 4 q
          (connDiffContrInsertionField (I := I) g₀ g₁)).toSection x)) :=
    funext fun x => armOuter_rfns_eq (I := I) (M := M) g₀ g₁ σ q x
  rw [hpt]

set_option linter.unusedSectionVars false in
private theorem armFull_norm_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)) (q : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 3 4 q
        (reindexCoeffGen (I := I) (M := M) g₀ 3 4
          (appCcRS (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ σ)
            (connDiffContrInsertionField (I := I) g₀ g₁)) ρ)‖ =
      ‖iteratedCovGrad (I := I) g₀ 3 4 q (connDiffContrInsertionField (I := I) g₀ g₁)‖ := by
  refine c3_norm_eq_of_sq_eq (norm_nonneg _) (norm_nonneg _) ?_
  rw [SmoothCcTensor.norm_def, SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 3 (4 + q)
      (iteratedCovGrad (I := I) g₀ 3 4 q
        (reindexCoeffGen (I := I) (M := M) g₀ 3 4
          (appCcRS (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ σ)
            (connDiffContrInsertionField (I := I) g₀ g₁)) ρ)),
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 3 (4 + q)
      (iteratedCovGrad (I := I) g₀ 3 4 q (connDiffContrInsertionField (I := I) g₀ g₁))]
  have hpt : (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + q) x
        ((iteratedCovGrad (I := I) g₀ 3 4 q
          (reindexCoeffGen (I := I) (M := M) g₀ 3 4
            (appCcRS (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ σ)
              (connDiffContrInsertionField (I := I) g₀ g₁)) ρ)).toSection x)) =
      (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + q) x
        ((iteratedCovGrad (I := I) g₀ 3 4 q
          (connDiffContrInsertionField (I := I) g₀ g₁)).toSection x)) :=
    funext fun x => armFull_rfns_eq (I := I) (M := M) g₀ g₁ σ ρ q x
  rw [hpt]

private lemma c3_norm_five_le {V : Type*} [SeminormedAddCommGroup V] {a b c d e : V} {n : ℝ}
    (ha : ‖a‖ = n) (hb : ‖b‖ = n) (hc : ‖c‖ = n) (hd : ‖d‖ = n) (he : ‖e‖ = n) :
    ‖a + b + c + d + e‖ ≤ 5 * n := by
  have t1 := norm_add_le (a + b + c + d) e
  have t2 := norm_add_le (a + b + c) d
  have t3 := norm_add_le (a + b) c
  have t4 := norm_add_le a b
  linarith

/-! ### Per-order structural bridge: Lie ≤ 5 · connDiff (squared: 25 ·) -/

set_option linter.unusedSectionVars false in
/-- Per-order structural bridge (generic in `g₁`): the Lie field's jet-L2 norm is bounded by
`5 ·` the connection-difference field's, because the Lie field is the negation of a sum of five
slot-permuted / reindexed copies of `connDiffContrInsertionField`, each an isometry of the jet.
Squared, this gives the `25 ·` factor threaded into the summed producer.  Mirrors the `h5`/`hsq`
block of `linearizedRicciConnDiffOrder1KernelField_order0sup_perOrder_l2_tameEnvelope_generic`. -/
private theorem lie_normSq_le_25 (g₀ g₁ : SmoothRiemannianMetric I M) (i : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 3 4 i
        (linearizedRicciConnDiffOrder1KernelField (I := I) g₀ g₁)‖ ^ 2 ≤
      25 * ‖iteratedCovGrad (I := I) g₀ 3 4 i
        (connDiffContrInsertionField (I := I) g₀ g₁)‖ ^ 2 := by
  have h5 : ‖iteratedCovGrad (I := I) g₀ 3 4 i
      (linearizedRicciConnDiffOrder1KernelField (I := I) g₀ g₁)‖ ≤
      5 * ‖iteratedCovGrad (I := I) g₀ 3 4 i
        (connDiffContrInsertionField (I := I) g₀ g₁)‖ := by
    rw [kernelField_eq_neg_arm_combination (I := I) g₀ g₁, iteratedCovGrad_neg, norm_neg,
      iteratedCovGrad_add, iteratedCovGrad_add, iteratedCovGrad_add, iteratedCovGrad_add]
    exact c3_norm_five_le
      (armFull_norm_eq (I := I) (M := M) g₀ g₁ kOutPerm0312 kInPerm102 i)
      (armFull_norm_eq (I := I) (M := M) g₀ g₁ kOutPerm0213 kInPerm120 i)
      (armOuter_norm_eq (I := I) (M := M) g₀ g₁ kOutPerm2301 i)
      (armFull_norm_eq (I := I) (M := M) g₀ g₁ kOutPerm1302 kInPerm102 i)
      (armFull_norm_eq (I := I) (M := M) g₀ g₁ kOutPerm1203 kInPerm120 i)
  have hsq := pow_le_pow_left₀ (norm_nonneg (iteratedCovGrad (I := I) g₀ 3 4 i
    (linearizedRicciConnDiffOrder1KernelField (I := I) g₀ g₁))) h5 2
  calc ‖iteratedCovGrad (I := I) g₀ 3 4 i
          (linearizedRicciConnDiffOrder1KernelField (I := I) g₀ g₁)‖ ^ 2
      ≤ (5 * ‖iteratedCovGrad (I := I) g₀ 3 4 i
          (connDiffContrInsertionField (I := I) g₀ g₁)‖) ^ 2 := hsq
    _ = 25 * ‖iteratedCovGrad (I := I) g₀ 3 4 i
          (connDiffContrInsertionField (I := I) g₀ g₁)‖ ^ 2 := by ring

/-! ### `realizedFam` per-order and summed bounds (REUSE of the connDiff producers). -/

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- `realizedFam` per-order top-separated bound for the Lie field: the connDiff per-order producer
composed with the `25 ·` structural bridge.  Top coefficient `Ktop = 25 · Ktop_connDiff` is
`R`-independent; the lumped low coefficient `Kc i = 25 · Kc_connDiff i` follows the house
`R`-pattern. -/
theorem linearizedRicciConnDiffOrder1KernelField_realizedFam_jetL2_perOrder_topSeparated
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
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
          ‖iteratedCovGrad (I := I) g₀ 3 4 i
              (linearizedRicciConnDiffOrder1KernelField (I := I) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 ≤
            Ktop * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T'‖ ^ 2) +
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  obtain ⟨Ktop, hKtop_nn, Kc, hKc_nn, hcd⟩ :=
    connDiffContrInsertionField_realizedFam_jetL2_perOrder_topSeparated
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨25 * Ktop, mul_nonneg (by norm_num) hKtop_nn,
    fun i => 25 * Kc i, fun i => mul_nonneg (by norm_num) (hKc_nn i), ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs i hi
  have hb := lie_normSq_le_25 (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) i
  have hc := hcd T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs i hi
  have h25 := mul_le_mul_of_nonneg_left hc (show (0 : ℝ) ≤ 25 by norm_num)
  calc ‖iteratedCovGrad (I := I) g₀ 3 4 i
          (linearizedRicciConnDiffOrder1KernelField (I := I) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2
      ≤ 25 * ‖iteratedCovGrad (I := I) g₀ 3 4 i
          (connDiffContrInsertionField (I := I) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 := hb
    _ ≤ 25 * (Ktop * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T'‖ ^ 2) +
          Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
            (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2))) := h25
    _ = 25 * Ktop * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T'‖ ^ 2) +
          25 * Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
            (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by ring

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- **Summed** data-weighted jet-L2 bound for the Lie field (constituent 4-of-5 of the
data-weighted threeArm precursor).  Sums the `25 ·` structural bridge over `i ≤ a` and reuses the
already-landed connDiff summed producer
`connDiffContrInsertionField_realizedFam_jetL2_summed_topSeparated` as a black box.  Both data
windows land at order `a+2`; `Ktop = 25 · Ktop_connDiff` is `R`-independent (the `5·`-triangle
squared times the `(g₀,hδ₀)`-only connDiff head), and `Kc = 25 · Kc_connDiff` follows the accepted
house `R`-pattern. -/
theorem linearizedRicciConnDiffOrder1KernelField_realizedFam_jetL2_summed_topSeparated
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
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
              ‖iteratedCovGrad (I := I) g₀ 3 4 i
                (linearizedRicciConnDiffOrder1KernelField (I := I) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 ≤
            Ktop * (∑ j ∈ Finset.range (a + 2),
                (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                  ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) +
            Kc * (1 + ∑ j ∈ Finset.range (a + 2),
                (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                  ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  obtain ⟨Ktop, hKtop_nn, Kc, hKc_nn, hcd⟩ :=
    connDiffContrInsertionField_realizedFam_jetL2_summed_topSeparated
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨25 * Ktop, mul_nonneg (by norm_num) hKtop_nn,
    25 * Kc, mul_nonneg (by norm_num) hKc_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs
  have hcd' := hcd T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs
  have hsum25 : ∑ i ∈ Finset.range (a + 1),
        ‖iteratedCovGrad (I := I) g₀ 3 4 i
          (linearizedRicciConnDiffOrder1KernelField (I := I) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 ≤
      25 * ∑ i ∈ Finset.range (a + 1),
        ‖iteratedCovGrad (I := I) g₀ 3 4 i
          (connDiffContrInsertionField (I := I) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ =>
      lie_normSq_le_25 (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) i)
  have h25 := mul_le_mul_of_nonneg_left hcd' (show (0 : ℝ) ≤ 25 by norm_num)
  calc ∑ i ∈ Finset.range (a + 1),
          ‖iteratedCovGrad (I := I) g₀ 3 4 i
            (linearizedRicciConnDiffOrder1KernelField (I := I) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2
      ≤ 25 * ∑ i ∈ Finset.range (a + 1),
          ‖iteratedCovGrad (I := I) g₀ 3 4 i
            (connDiffContrInsertionField (I := I) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 := hsum25
    _ ≤ 25 * (Ktop * (∑ j ∈ Finset.range (a + 2),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) +
            Kc * (1 + ∑ j ∈ Finset.range (a + 2),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2))) := h25
    _ = 25 * Ktop * (∑ j ∈ Finset.range (a + 2),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) +
          25 * Kc * (1 + ∑ j ∈ Finset.range (a + 2),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by ring

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
