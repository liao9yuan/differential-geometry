import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.PointwiseToL2Packaging

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open TensorRSNabla
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization (gFibreOpBound
    ccTensorBilinSymm tensorSectionRealizeMetric)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-!
## Uniform covariant-jet bound for the g1-inverse sharp-field arm

The consumer `deTurckRHSArmDiff_threeArm_coeffC0_jetL2_ballUniform` (in
`DeTurckRemainderTameLipschitz.lean`, conjunct (c)) needs a uniform L² bound
`∑_{i ∈ range(a+1)} ‖iteratedCovGrad g0 (rank) i Cₖ‖² ≤ Γ²` for the coefficient
arm `Cₖ` built from the inverse of the realized metric `g1 = tensorSectionRealizeMetric`.
That arm is `connDiffGInvComposite g0 g1 : SmoothCcTensor g0 1 2` (the slot-coefficient
whose fibre is `connDiffGInvCompositeFib`, equivalently the g1⁻¹ sharp field packaged
in the `(1,2)` slot that the `appCc`/`appCcRS` diagonal-product-grid multiplies).

This file provides that uniform bound in two layers:

* `rfns_iteratedCovGrad_connDiffGInvComposite_uniform_le` (deferred leaf) — the pointwise
  fibre-norm strong-induction bound.
* `l2Sum_iteratedCovGrad_connDiffGInvComposite_uniform_le` (proven glue) — integrates
  the pointwise bound over the compact manifold to produce the L²-sum form the consumer
  accepts, via the standard finite-measure pointwise-to-L² packaging.
-/

/-- Explicit uniform pointwise bound polynomial for the g1⁻¹ sharp-field covariant jet.

An explicit function of the curvature scale `R`, the perturbation size `δ`, and the jet
order `i` — a polynomial in `R`, `Module.finrank ℝ E`, and `(1/(1-δ))^(i+2)`. It is NOT
`Classical.choose` or a T-dependent compactness supremum, so it preserves uniformity in
the perturbation `T`. -/
noncomputable def gInvSharpJetBound (R δ : ℝ) (i : ℕ) : ℝ :=
  (Module.finrank ℝ E : ℝ) ^ 2 * (1 + R) ^ (2 * i + 4) * (1 / (1 - δ)) ^ (4 * i + 8)

lemma gInvSharpJetBound_nonneg (R δ : ℝ) (hR : 0 ≤ R) (hδ : δ < 1) (i : ℕ) :
    0 ≤ gInvSharpJetBound (E := E) R δ i := by
  have hpos : 0 < 1 - δ := by linarith
  have hinv_nn : 0 ≤ 1 / (1 - δ) := by positivity
  simp only [gInvSharpJetBound]
  apply mul_nonneg
  · apply mul_nonneg
    · exact pow_nonneg (Nat.cast_nonneg _) 2
    · exact pow_nonneg (by linarith) (2 * i + 4)
  · exact pow_nonneg hinv_nn (4 * i + 8)

/-- The pointwise bound is monotone increasing in the perturbation size: larger `δ`
(closer to 1) gives a larger jet bound, since `1/(1-δ)` grows. This is pure algebra on
`1/(1-δ)` and is sign-agnostic in `δ` (only `δ < 1` and `δ ≤ δ'` are needed). -/
theorem gInvSharpJetBound_mono_δ (R δ δ' : ℝ) (hR : 0 ≤ R) (hδ_lt : δ < 1) (hδ' : δ ≤ δ')
    (hδ'_lt : δ' < 1) (i : ℕ) :
    gInvSharpJetBound (E := E) R δ i ≤ gInvSharpJetBound (E := E) R δ' i := by
  have hpos_δ : 0 < 1 - δ := by linarith
  have hpos_δ' : 0 < 1 - δ' := by linarith
  have hinv_δ_nn : 0 ≤ 1 / (1 - δ) := by positivity
  have hinv_δ'_nn : 0 ≤ 1 / (1 - δ') := by positivity
  have hr_inv : 1 / (1 - δ) ≤ 1 / (1 - δ') :=
    (one_div_le_one_div hpos_δ hpos_δ').mpr (by linarith)
  simp only [gInvSharpJetBound]
  apply mul_le_mul_of_nonneg_left
  · induction 4 * i + 8 with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, pow_succ]
      exact mul_le_mul ih hr_inv hinv_δ_nn (pow_nonneg hinv_δ'_nn n)
  · apply mul_nonneg
    · exact pow_nonneg (Nat.cast_nonneg _) 2
    · exact pow_nonneg (by linarith) (2 * i + 4)

/-- Consumer-minimal child: the simultaneous strong-induction form of the g1⁻¹
sharp-field iterated-jet bound, giving the bound for ALL orders up to `i` at once.

This is the natural strong-induction statement (the hypothesis shape): proving the bound
at order `i` consumes the bound at every order `< i`. It is genuinely different from the
single-order conclusion of the target leaf, which the glue extracts by specialization.
Genuine self-referential induction leaf. The single-step identity
`covGrad_gInvDiffSlotCoeff_eq_appCcRS_composite` expresses
`∇(g1⁻¹ slot) = -connDiffGInvComposite · (g1⁻¹ slot) + 0-order connDiff arm`; iterating
via the covariant Leibniz `iteratedCovGrad_appCcRS_eq` expands `∇ᵏ(g1⁻¹)` into binomial
products of lower-order g1⁻¹ factors (order `< k`, by this lemma) and connDiff factors
(bounded via `covDerivConnDiff_g1inner_eq_secondCovGrad_lowerArms`, whose Koszul
structure has no same-order `∇connDiff` term). The g1-cometric parallelism
`inverseMetricSharpField_covGrad_eq_zero` kills the same-order self-term. Base case
`k = 0` is `riemannianFiberNormSq_gInvSlotEndo_le`. Strictly order-decreasing on both
factor families, so the induction is well-founded and closes against
`gInvSharpJetBound R δ k`. -/
private theorem rfns_iteratedCovGrad_gInvSlotEndo_allOrders_uniform_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {R : ℝ} (hR : 0 ≤ R) {δ₀ : ℝ} (hδ₀ : δ₀ < 1)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_le : δ ≤ δ₀)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ_lt : δ < 1)
    (hTjet : ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R)
    (i : ℕ) (hi : i ≤ a + 1) (x : M) :
    ∀ k : ℕ, k ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + k) x
          ((iteratedCovGrad (I := I) g₀ 1 2 k
            (connDiffGInvComposite (I := I) g₀
              (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ))).toSection x) ≤
        gInvSharpJetBound (E := E) R δ k := by
  sorry

/-- Deferred leaf: the uniform pointwise fibre-norm bound on the g1⁻¹ sharp-field
covariant jet, of order `i`, uniformly over the perturbation `T`.

This is the assembly glue: it specializes the simultaneous strong-induction child
`rfns_iteratedCovGrad_gInvSlotEndo_allOrders_uniform_le` (which carries the bound for
ALL orders `k ≤ i`, the natural induction-hypothesis shape) to the target order
`k = i`. The child is the genuine self-referential induction leaf; this theorem is its
single-order projection. -/
theorem rfns_iteratedCovGrad_connDiffGInvComposite_uniform_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {R : ℝ} (hR : 0 ≤ R) {δ₀ : ℝ} (hδ₀ : δ₀ < 1)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_le : δ ≤ δ₀)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ_lt : δ < 1)
    (hTjet : ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R)
    (i : ℕ) (hi : i ≤ a + 1) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 2 i
          (connDiffGInvComposite (I := I) g₀
            (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ))).toSection x) ≤
      gInvSharpJetBound (E := E) R δ i := by
  exact rfns_iteratedCovGrad_gInvSlotEndo_allOrders_uniform_le
    (I := I) g₀ a ha_super hR hδ₀ T hδ_le hδ hδ_lt hTjet i hi x i (le_refl i)

/-- Uniform L²-sum bound for the g1⁻¹ sharp-field covariant jet, in the form the
consumer `deTurckRHSArmDiff_threeArm_coeffC0_jetL2_ballUniform` (conjunct (c)) accepts:
a single uniform constant `Γ` (depending only on `a`, `R`, `δ₀`, `g₀`, not on `T` or `δ`)
such that the sum of squared L² norms of the first `a+1` covariant derivatives of the
g1⁻¹ sharp-field arm is bounded by `Γ²`.

This is the proven glue: it packages the pointwise uniform bound
`rfns_iteratedCovGrad_connDiffGInvComposite_uniform_le` into the L²-sum form via the
standard finite-measure pointwise-to-L² packaging on the compact manifold. -/
theorem l2Sum_iteratedCovGrad_connDiffGInvComposite_uniform_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {R : ℝ} (hR : 0 ≤ R) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Γ : ℝ, 0 ≤ Γ ∧
      ∀ (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδ_lt : δ < 1)
        (hTjet : ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R),
        ∑ i ∈ Finset.range (a + 1),
            ‖iteratedCovGrad (I := I) g₀ 1 2 i
              (connDiffGInvComposite (I := I) g₀
                (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ))‖ ^ 2 ≤
          Γ ^ 2 := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  set V : ℝ := (riemannianVolumeMeasure (I := I) (M := M) g₀ Set.univ).toReal with hV_def
  have hV_nn : 0 ≤ V := ENNReal.toReal_nonneg
  set P : ℕ → ℝ := gInvSharpJetBound (E := E) R δ₀ with hP_def
  set Γ : ℝ := Real.sqrt (V * ∑ i ∈ Finset.range (a + 1), P i) with hΓ_def
  refine ⟨Γ, ?_, ?_⟩
  · -- non-negativity of Γ
    have hPsum_nn : 0 ≤ ∑ i ∈ Finset.range (a + 1), P i :=
      Finset.sum_nonneg (fun i _ => gInvSharpJetBound_nonneg R δ₀ hR hδ₀ i)
    have hVP_nn : 0 ≤ V * ∑ i ∈ Finset.range (a + 1), P i :=
      mul_nonneg hV_nn hPsum_nn
    exact Real.sqrt_nonneg _
  · intro T δ hδ_le hδ hδ_lt hTjet
    set g₁ := tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ with hg₁_def
    -- Per-order: ‖∇ⁱC‖² ≤ (rfns bound at δ) * V ≤ P i * V, via pointwise-to-L² packaging.
    -- The δ → δ₀ step uses the sign-agnostic monotonicity (only needs δ < 1, δ ≤ δ₀).
    have hper_order : ∀ i ∈ Finset.range (a + 1),
        ‖iteratedCovGrad (I := I) g₀ 1 2 i
          (connDiffGInvComposite (I := I) g₀ g₁)‖ ^ 2 ≤ P i * V := by
      intro i hi
      have hi_le : i ≤ a + 1 := (Finset.mem_range.mp hi).le
      set Ci := iteratedCovGrad (I := I) g₀ 1 2 i (connDiffGInvComposite (I := I) g₀ g₁)
      have hptwise : ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x (Ci.toSection x) ≤
            gInvSharpJetBound R δ i :=
        fun x => rfns_iteratedCovGrad_connDiffGInvComposite_uniform_le
          (I := I) g₀ a ha_super hR hδ₀ T hδ_le hδ hδ_lt hTjet i hi_le x
      have hPle : gInvSharpJetBound R δ i ≤ P i :=
        gInvSharpJetBound_mono_δ R δ δ₀ hR hδ_lt hδ_le hδ₀ i
      have hptwise_P : ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x (Ci.toSection x) ≤ P i :=
        fun x => (hptwise x).trans hPle
      have hCi_PiV : ‖Ci‖ ^ 2 ≤ P i * V := by
        have hbd := norm_le_of_pointwise_fiberNormSq_bound_rs (I := I) g₀ 1 (2 + i) Ci (P i)
          hptwise_P
        calc ‖Ci‖ ^ 2
            ≤ P i * (riemannianVolumeMeasure (I := I) (M := M) g₀ Set.univ).toReal := hbd
          _ = P i * V := by rw [hV_def]
      exact hCi_PiV
    have hPsum_nn : 0 ≤ ∑ i ∈ Finset.range (a + 1), P i :=
      Finset.sum_nonneg (fun i _ => gInvSharpJetBound_nonneg R δ₀ hR hδ₀ i)
    have hVP_nn : 0 ≤ V * ∑ i ∈ Finset.range (a + 1), P i :=
      mul_nonneg hV_nn hPsum_nn
    have hΓ_sq : Γ ^ 2 = V * ∑ i ∈ Finset.range (a + 1), P i := by
      unfold Γ
      exact Real.sq_sqrt hVP_nn
    calc ∑ i ∈ Finset.range (a + 1),
            ‖iteratedCovGrad (I := I) g₀ 1 2 i
              (connDiffGInvComposite (I := I) g₀ g₁)‖ ^ 2
        ≤ ∑ i ∈ Finset.range (a + 1), P i * V :=
            Finset.sum_le_sum (fun i hi => hper_order i hi)
      _ = (∑ i ∈ Finset.range (a + 1), P i) * V := by rw [Finset.sum_mul]
      _ = V * ∑ i ∈ Finset.range (a + 1), P i := by ring
      _ = Γ ^ 2 := by rw [hΓ_sq]

end Connection
end Integral
end DifferentialGeometry

end
