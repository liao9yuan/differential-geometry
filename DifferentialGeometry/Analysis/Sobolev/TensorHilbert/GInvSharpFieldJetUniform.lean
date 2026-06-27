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
  ((2 * ((Module.finrank ℝ E : ℝ) + 1)) ^ (4 * i + 8) * (Module.finrank ℝ E : ℝ) ^ 2 *
      ((i : ℝ) + 1) ^ 4 * (1 + R) ^ (3 * i + 6)) * (1 / (1 - δ)) ^ (4 * i + 8)

lemma gInvSharpJetBound_prefactor_nonneg (R : ℝ) (hR : 0 ≤ R) (i : ℕ) :
    0 ≤ (2 * ((Module.finrank ℝ E : ℝ) + 1)) ^ (4 * i + 8) * (Module.finrank ℝ E : ℝ) ^ 2 *
        ((i : ℝ) + 1) ^ 4 * (1 + R) ^ (3 * i + 6) := by
  have hgrid_nn : (0 : ℝ) ≤ 2 * ((Module.finrank ℝ E : ℝ) + 1) := by positivity
  apply mul_nonneg
  · apply mul_nonneg
    · apply mul_nonneg
      · exact pow_nonneg hgrid_nn (4 * i + 8)
      · exact pow_nonneg (Nat.cast_nonneg _) 2
    · exact pow_nonneg (by positivity) 4
  · exact pow_nonneg (by linarith) (3 * i + 6)

lemma gInvSharpJetBound_nonneg (R δ : ℝ) (hR : 0 ≤ R) (hδ : δ < 1) (i : ℕ) :
    0 ≤ gInvSharpJetBound (E := E) R δ i := by
  have hpos : 0 < 1 - δ := by linarith
  have hinv_nn : 0 ≤ 1 / (1 - δ) := by positivity
  simp only [gInvSharpJetBound]
  apply mul_nonneg
  · exact gInvSharpJetBound_prefactor_nonneg R hR i
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
  · exact gInvSharpJetBound_prefactor_nonneg R hR i

/-- Consumer-minimal child (POSIT): the single covariant-jet step for the g1⁻¹ sharp-field
composite arm. Given the order-`k` pointwise rfns bound at EVERY order `j ≤ k` (the
strong-induction hypothesis, the previous orders of the inverse jet), the order-`(k+1)`
rfns is bounded by the next-order jet budget `gInvSharpJetBound R δ (k+1)`.

This is the genuine irreducible inverse-jet recursion. `connDiffGInvComposite g₀ g₁` is
`connDiff(g₁,g₀)` precomposed in its slot-0 tangent input by the inverse-metric
endomorphism `gInvRaisedEndo g₀ g₁`. Its covariant derivative — taken with the
`g₀`-Levi-Civita connection — is governed by `covGrad_gInvDiffSlotCoeff_eq_appCcRS_composite`
(the only on-disk single-step identity touching this arm): `∇^{g₀}(g₁⁻¹ endo)` equals
`-connDiffGInvComposite·(g₁⁻¹ endo)` plus the order-0 connDiff/inverse-sharp correction,
because the `g₁`-cometric is `g₁`-parallel (`inverseMetricSharpField_covGrad_eq_zero`) so
the only contribution is the Christoffel-difference term `connDiff = Γ₁ − Γ₀`. Iterating
via the covariant Leibniz `iteratedCovGrad_appCcRS_eq` through the diagonal-product grid
`rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le` expands `∇^{k+1}` into a
binomial sum of strictly-lower-order inverse factors (order `≤ k`, bounded by the IH
`hIH`) times connDiff factors (whose all-orders Koszul rfns is jet-budget-bounded via
`covDerivConnDiff_g1inner_eq_secondCovGrad_lowerArms`). The `appCcGdiag(k)=(2(finrank+1))^k`
grid prefactor is exactly what the corrected `gInvSharpJetBound` finrank-grid exponent
`4k+8` absorbs; the budget closes by `diagonalGrid_power_closure`. Strictly
order-decreasing, so the parent strong induction is well-founded. -/
private theorem rfns_iteratedCovGrad_connDiffGInvComposite_succ_step
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {R : ℝ} (hR : 0 ≤ R) {δ₀ : ℝ} (hδ₀ : δ₀ < 1)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_le : δ ≤ δ₀)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ_lt : δ < 1)
    (hTjet_pt : ∀ j : ℕ, j ≤ a + 2 → ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) y
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection y) ≤ R ^ 2)
    (k : ℕ) (hk : k + 1 ≤ a + 1) (x : M)
    (hIH : ∀ j : ℕ, j ≤ k →
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 1 2 j
            (connDiffGInvComposite (I := I) g₀
              (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ))).toSection x) ≤
        gInvSharpJetBound (E := E) R δ j) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + (k + 1)) x
        ((iteratedCovGrad (I := I) g₀ 1 2 (k + 1)
          (connDiffGInvComposite (I := I) g₀
            (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ))).toSection x) ≤
      gInvSharpJetBound (E := E) R δ (k + 1) := by
  sorry

/-- Consumer-minimal child (POSIT): the order-0 (C⁰) pointwise rfns bound for the g1⁻¹
sharp-field composite arm — the base case of the inverse-jet induction. The order-0 of
`connDiffGInvComposite g₀ g₁` is `connDiff(g₁,g₀)·gInvRaisedEndo`, a single contraction of
the Christoffel-difference (rfns `~ finrank³·(1+δ₀)²·‖∇¹T‖² ≤ finrank³·(1+R)²·R²`) with the
inverse-metric endomorphism (rfns `≤ (finrank·1/(1-δ))²`). The product is bounded by
`gInvSharpJetBound R δ 0`, whose `(2(finrank+1))^8·finrank²·(1+R)^6·(1/(1-δ))^8`
generously dominates the order-0 product. -/
private theorem rfns_iteratedCovGrad_connDiffGInvComposite_base
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {R : ℝ} (hR : 0 ≤ R) {δ₀ : ℝ} (hδ₀ : δ₀ < 1)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_le : δ ≤ δ₀)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ_lt : δ < 1)
    (hTjet_pt : ∀ j : ℕ, j ≤ a + 2 → ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) y
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection y) ≤ R ^ 2)
    (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + 0) x
        ((iteratedCovGrad (I := I) g₀ 1 2 0
          (connDiffGInvComposite (I := I) g₀
            (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ))).toSection x) ≤
      gInvSharpJetBound (E := E) R δ 0 := by
  sorry

/-- Consumer-minimal child: the simultaneous strong-induction form of the g1⁻¹
sharp-field iterated-jet bound, giving the bound for ALL orders up to `i` at once.

This is the proven assembly glue over the genuine recursion children: a `Nat`-strong
induction on the order `k`. The base case `k = 0` is
`rfns_iteratedCovGrad_connDiffGInvComposite_base`; the successor step
`rfns_iteratedCovGrad_connDiffGInvComposite_succ_step` consumes the bound at every order
`≤ k` (the strong-induction hypothesis) and produces order `k + 1`. -/
private theorem rfns_iteratedCovGrad_gInvSlotEndo_allOrders_uniform_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {R : ℝ} (hR : 0 ≤ R) {δ₀ : ℝ} (hδ₀ : δ₀ < 1)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_le : δ ≤ δ₀)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ_lt : δ < 1)
    (hTjet_pt : ∀ j : ℕ, j ≤ a + 2 → ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) y
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection y) ≤ R ^ 2)
    (i : ℕ) (hi : i ≤ a + 1) (x : M) :
    ∀ k : ℕ, k ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + k) x
          ((iteratedCovGrad (I := I) g₀ 1 2 k
            (connDiffGInvComposite (I := I) g₀
              (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ))).toSection x) ≤
        gInvSharpJetBound (E := E) R δ k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k hstrong =>
    intro hk_le
    match k, hk_le with
    | 0, _ =>
        exact rfns_iteratedCovGrad_connDiffGInvComposite_base
          (I := I) g₀ a ha_super hR hδ₀ T hδ_le hδ hδ_lt hTjet_pt x
    | (k + 1), hk_le =>
        have hk1_le_a1 : k + 1 ≤ a + 1 := le_trans hk_le hi
        refine rfns_iteratedCovGrad_connDiffGInvComposite_succ_step
          (I := I) g₀ a ha_super hR hδ₀ T hδ_le hδ hδ_lt hTjet_pt k hk1_le_a1 x ?_
        intro j hj
        exact hstrong j (Nat.lt_succ_of_le hj) (le_trans hj (le_trans (Nat.le_succ k) hk_le))

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
    (hTjet_pt : ∀ j : ℕ, j ≤ a + 2 → ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) y
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection y) ≤ R ^ 2)
    (i : ℕ) (hi : i ≤ a + 1) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 2 i
          (connDiffGInvComposite (I := I) g₀
            (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ))).toSection x) ≤
      gInvSharpJetBound (E := E) R δ i := by
  exact rfns_iteratedCovGrad_gInvSlotEndo_allOrders_uniform_le
    (I := I) g₀ a ha_super hR hδ₀ T hδ_le hδ hδ_lt hTjet_pt i hi x i (le_refl i)

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
        (hTjet_pt : ∀ j : ℕ, j ≤ a + 2 → ∀ y : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) y
            ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection y) ≤ R ^ 2),
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
  ·
    have hPsum_nn : 0 ≤ ∑ i ∈ Finset.range (a + 1), P i :=
      Finset.sum_nonneg (fun i _ => gInvSharpJetBound_nonneg R δ₀ hR hδ₀ i)
    have hVP_nn : 0 ≤ V * ∑ i ∈ Finset.range (a + 1), P i :=
      mul_nonneg hV_nn hPsum_nn
    exact Real.sqrt_nonneg _
  · intro T δ hδ_le hδ hδ_lt hTjet_pt
    set g₁ := tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ with hg₁_def
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
          (I := I) g₀ a ha_super hR hδ₀ T hδ_le hδ hδ_lt hTjet_pt i hi_le x
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
