import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.L2Bound
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingReverseHebey

/-!
# The quantitative order-`2` chart-`H²` Gårding constant for `(0, 2)`-tensors

For a closed smooth Riemannian manifold `(M, g)` modelled on a real inner-product space `E`,
this file assembles the **quantitative order-`2` (chart-`H²`) Gårding estimate** for smooth
compactly-supported `(0, 2)`-tensor fields:

```
‖T‖_{H²_intrinsic} ≤ C · (‖Δ_∇ T‖_{L²} + ‖T‖_{L²}),     C ≥ 0 independent of T,
```

where `‖·‖_{H²_intrinsic} = tensorPouSobolevHsNorm g 1` is the intrinsic order-`2`
partition-of-unity-weighted chart-Sobolev (Hilbert–Schmidt) norm, `Δ_∇ T =
rawTensorConnLapSmooth g 0 2 T` is the rough (connection) Laplacian, and all `L²` norms are the
intrinsic metric `L²` norms `‖SmoothCcTensor.toL2 ·‖`. This is exactly the *hard* direction of
the order-`2` Gårding/elliptic-regularity comparison isolated as `Order2NormEquivOnSmooth`
(`Analysis/Spectral/Tensor/SobolevScale/Order2Equivalence.lean`), and the `k = 1` instance of the
all-orders elliptic hypothesis `h_elliptic` of `eigenSpan_pouHs_le_spectral_of_elliptic`
(`Analysis/Spectral/Intrinsic/Garding/EigenComboGardingReduction.lean`). It is the single
analytic input the smooth-representative gate needs along the Gårding + Sobolev-embedding route
(which avoids the local Weyl law).

## The assembly

The estimate chains three pieces:

1. The **covariant** order-`2` Gårding constant `exists_secondCovGrad_l2NormSq_le_rawConnLap`:
   `‖∇²T‖²_{L²} ≤ Cg · (‖Δ_∇ T‖²_{L²} + ‖T‖²_{L²})`, obtained from the conditional Gårding
   reduction `secondCovGrad_l2NormSq_le_rawConnLap_of_pointwise_curv_bound`
   (`Geometry/Curvature/CovGradRoughLap/L2Bound.lean`) fed the pointwise curvature-defect
   fibre-norm bound on `covGradRoughLapCurv g T`.

2. The **order-`1`** covariant-gradient control `covGrad_l2NormSq_le_rawConnLap_mul_self_gen`
   (`IntegratedOrder2Garding.lean`): `‖∇T‖²_{L²} ≤ ‖Δ_∇ T‖_{L²} · ‖T‖_{L²}`.

3. The **reverse Hebey–Sobolev bridge**
   `exists_tensorPouSobolevHsNorm_toReal_le_iteratedCovGrad_tensorL2Norm_sum`
   (`Analysis/Sobolev/Embedding/SobolevEmbeddingReverseHebey.lean`): for every `(r, s, k)`,
   `(tensorPouSobolevHsNorm g k T).toReal ≤ C · ∑_{j ≤ 2k} ‖∇^j T‖_{L²}`. At `k = 1`, `(r, s) =
   (0, 2)` the sum runs over `j ∈ {0, 1, 2}`, i.e. `‖T‖_{L²} + ‖∇T‖_{L²} + ‖∇²T‖_{L²}`.

Substituting (1) and (2) into (3) and absorbing the resulting square roots with the elementary
`√(a·b) ≤ (a + b)/2` and `√(a² + b²) ≤ a + b` inequalities (`a, b ≥ 0`) collapses the
right-hand side to a multiple of `‖Δ_∇ T‖_{L²} + ‖T‖_{L²}`.

## The single remaining analytic input (posited, not assumed in a headline)

The covariant Gårding constant (1) rests on the **pointwise** curvature-defect fibre-norm bound
`covGradRoughLapCurv_pointwise_fiberNormSq_bound`: there is `C₀ ≥ 0` with
```
rfns(Δ_∇(∇T) − ∇(Δ_∇ T))(x) ≤ C₀² · (rfns(T) + rfns(∇T) + rfns(∇²T))(x)     for all x.
```
This is the genuine third-order tensor Weitzenböck content documented as the precise remaining
subgoal across `CovGradRoughLap/{CurvatureDefect, L2Bound}.lean` and `Order2Defect/{MetricTraceFrame,
SlotSplitBound}.lean` (the slot-`0` Christoffel matching together with the moving-frame residual
cancellation). It is the *only* `sorry` in this file's dependency cone for the new declarations; it
is isolated as one honestly-labelled deferred input, never assumed in a headline. Closing it makes
the entire chart-`H²` Gårding constant unconditional with no further work.

## Sign / order conventions

Geometer convention `Δ_∇ = -∇*∇` for the rough Laplacian `rawTensorConnLapSmooth`. The covariant
gradient `covGrad g 0 s` raises the tensor rank from `(0, s)` to `(0, s + 1)`; `∇^j` is
`iteratedCovGrad g 0 2 j`. "Order `2`" / "chart-`H²`" is the project index-`1` space
`tensorPouSobolevHsNorm g 1` (the sum runs to `2k = 2`).
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- **The pointwise curvature-defect fibre-norm bound (deferred analytic input).** There is a
nonnegative constant `C₀` such that, for every smooth compactly-supported `(0, 2)`-tensor field
`T` and every `x`, the canonical rough-Laplacian / covariant-gradient commutator defect
`covGradRoughLapCurv g T = Δ_∇(∇T) − ∇(Δ_∇ T)` is controlled fibrewise by the first-order Sobolev
budget of `T`:
```
rfns(covGradRoughLapCurv g T)(x)
  ≤ C₀² · (rfns(T) + rfns(∇T) + rfns(∇²T))(x).
```

This is the genuine third-order tensor Weitzenböck content (the slot-`0` Christoffel matching plus
the moving-frame residual cancellation) documented as the precise remaining subgoal across
`CovGradRoughLap/{CurvatureDefect, L2Bound}.lean` and `Order2Defect/{MetricTraceFrame,
SlotSplitBound}.lean`. It is posited here as a single, honestly-labelled deferred input and is the
*only* `sorry` underlying every other declaration in this file; closing it makes the whole chart-`H²`
Gårding constant unconditional. The constant `C₀` is uniform in `T` because the canonical defect is
`ℝ`-linear in `T` and the curvature operator is uniformly bounded on the compact manifold. -/
theorem covGradRoughLapCurv_pointwise_fiberNormSq_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∀ (T : SmoothCcTensor g 0 2) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 3 x
            ((covGradRoughLapCurv (I := I) (M := M) g T).toSection x) ≤
          C₀ ^ 2 *
            (riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T.toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 3 x
                ((covGrad (I := I) (M := M) g 0 2 T).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 (3 + 1) x
                ((covGrad (I := I) (M := M) g 0 3
                  (covGrad (I := I) (M := M) g 0 2 T)).toSection x)) :=
  sorry

set_option linter.unusedSectionVars false in
/-- **The covariant order-`2` Gårding constant.** There is a nonnegative constant `Cg`, uniform in
`T`, with
```
‖∇²T‖²_{L²} ≤ Cg · (‖Δ_∇ T‖²_{L²} + ‖T‖²_{L²})
```
for every smooth compactly-supported `(0, 2)`-tensor field `T`, where `∇²T = covGrad g 0 3 (covGrad
g 0 2 T)`. This is the conditional Gårding reduction
`secondCovGrad_l2NormSq_le_rawConnLap_of_pointwise_curv_bound` fed the (deferred) pointwise
curvature-defect fibre-norm bound `covGradRoughLapCurv_pointwise_fiberNormSq_bound`; the constant
`Cg = 2 + 3 C₀ + 2 C₀²` carries the curvature defect and the Young/absorption bookkeeping. -/
theorem exists_secondCovGrad_l2NormSq_le_rawConnLap
    (g : SmoothRiemannianMetric I M) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧
      ∀ T : SmoothCcTensor g 0 2,
        tensorL2Norm (I := I) (M := M) g 0 (3 + 1)
            (covGrad (I := I) (M := M) g 0 3
              (covGrad (I := I) (M := M) g 0 2 T)).toFun ^ 2 ≤
          Cg *
            (tensorL2Norm (I := I) (M := M) g 0 2
                (rawTensorConnLapSmooth (I := I) g 0 2 T).toFun ^ 2 +
              tensorL2Norm (I := I) (M := M) g 0 2 T.toFun ^ 2) := by
  obtain ⟨C₀, hC₀, hpt⟩ := covGradRoughLapCurv_pointwise_fiberNormSq_bound (I := I) (M := M) g
  refine ⟨2 + 3 * C₀ + 2 * C₀ ^ 2, by positivity, fun T => ?_⟩
  exact secondCovGrad_l2NormSq_le_rawConnLap_of_pointwise_curv_bound (I := I) (M := M) g T C₀ hC₀
    (hpt T)

set_option linter.unusedSectionVars false in
/-- **The covariant order-`2` Gårding constant, square-rooted (linear) form.** There is a
nonnegative constant `Cg`, uniform in `T`, with
```
‖∇²T‖_{L²} ≤ Cg · (‖Δ_∇ T‖_{L²} + ‖T‖_{L²})
```
for every smooth compactly-supported `(0, 2)`-tensor field `T`. This is the square root of
`exists_secondCovGrad_l2NormSq_le_rawConnLap` together with `√(a · (p² + q²)) ≤ √a · (p + q)`
(`a, p, q ≥ 0`). -/
theorem exists_secondCovGrad_l2Norm_le_rawConnLap_add_self
    (g : SmoothRiemannianMetric I M) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧
      ∀ T : SmoothCcTensor g 0 2,
        tensorL2Norm (I := I) (M := M) g 0 (3 + 1)
            (covGrad (I := I) (M := M) g 0 3
              (covGrad (I := I) (M := M) g 0 2 T)).toFun ≤
          Cg *
            (tensorL2Norm (I := I) (M := M) g 0 2
                (rawTensorConnLapSmooth (I := I) g 0 2 T).toFun +
              tensorL2Norm (I := I) (M := M) g 0 2 T.toFun) := by
  obtain ⟨Cg, hCg, hbound⟩ := exists_secondCovGrad_l2NormSq_le_rawConnLap (I := I) (M := M) g
  refine ⟨Real.sqrt Cg, Real.sqrt_nonneg _, fun T => ?_⟩
  set nHess : ℝ := tensorL2Norm (I := I) (M := M) g 0 (3 + 1)
    (covGrad (I := I) (M := M) g 0 3 (covGrad (I := I) (M := M) g 0 2 T)).toFun with hnHess_def
  set nLap : ℝ := tensorL2Norm (I := I) (M := M) g 0 2
    (rawTensorConnLapSmooth (I := I) g 0 2 T).toFun with hnLap_def
  set nT : ℝ := tensorL2Norm (I := I) (M := M) g 0 2 T.toFun with hnT_def
  have hnHess_nn : 0 ≤ nHess := tensorL2Norm_nonneg (I := I) (M := M) g 0 (3 + 1) _
  have hnLap_nn : 0 ≤ nLap := tensorL2Norm_nonneg (I := I) (M := M) g 0 2 _
  have hnT_nn : 0 ≤ nT := tensorL2Norm_nonneg (I := I) (M := M) g 0 2 _
  have hsq : nHess ^ 2 ≤ Cg * (nLap ^ 2 + nT ^ 2) := hbound T
  have hkey : nHess ^ 2 ≤ (Real.sqrt Cg * (nLap + nT)) ^ 2 := by
    have hsqrtCg : Real.sqrt Cg ^ 2 = Cg := Real.sq_sqrt hCg
    have hexpand : (Real.sqrt Cg * (nLap + nT)) ^ 2 =
        Cg * (nLap ^ 2 + 2 * (nLap * nT) + nT ^ 2) := by
      rw [mul_pow, hsqrtCg]; ring
    rw [hexpand]
    have hcross_nn : 0 ≤ 2 * (nLap * nT) := by positivity
    nlinarith [hsq, mul_le_mul_of_nonneg_left hcross_nn hCg, hCg]
  have hrhs_nn : 0 ≤ Real.sqrt Cg * (nLap + nT) :=
    mul_nonneg (Real.sqrt_nonneg _) (by linarith)
  exact le_of_sq_le_sq hkey hrhs_nn

set_option linter.unusedSectionVars false in
/-- **The quantitative chart-`H²` Gårding constant (clean linear form).** There is a nonnegative
constant `C`, uniform in `T`, with
```
(tensorPouSobolevHsNorm g 1 T).toReal ≤ C · (‖Δ_∇ T‖_{L²} + ‖T‖_{L²})
```
for every smooth compactly-supported `(0, 2)`-tensor field `T`, where `‖·‖_{L²} = ‖SmoothCcTensor.toL2
·‖` is the intrinsic metric `L²` norm. This is the hard direction of the order-`2`
Gårding/elliptic-regularity comparison.

The proof feeds the covariant order-`2` Gårding bound
`exists_secondCovGrad_l2Norm_le_rawConnLap_add_self` (`‖∇²T‖ ≤ Cg·(‖Δ_∇T‖ + ‖T‖)`) and the
order-`1` control `covGrad_l2NormSq_le_rawConnLap_mul_self_gen` (`‖∇T‖² ≤ ‖Δ_∇T‖·‖T‖`) into the
reverse Hebey–Sobolev bridge
`exists_tensorPouSobolevHsNorm_toReal_le_iteratedCovGrad_tensorL2Norm_sum` (at `k = 1`,
`(r, s) = (0, 2)`), whose `j ∈ {0, 1, 2}` sum is `‖T‖_{L²} + ‖∇T‖_{L²} + ‖∇²T‖_{L²}`, and absorbs
the `‖∇T‖ ≤ √(‖Δ_∇T‖·‖T‖) ≤ (‖Δ_∇T‖ + ‖T‖)/2` term. -/
theorem exists_tensorPouSobolevHsNorm_one_le_rawConnLap_add_self
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : SmoothCcTensor g 0 2,
        (tensorPouSobolevHsNorm (I := I) (M := M) g 1 T).toReal ≤
          C * (‖SmoothCcTensor.toL2 (rawTensorConnLapSmooth (I := I) g 0 2 T)‖ +
            ‖SmoothCcTensor.toL2 T‖) := by
  classical
  obtain ⟨Cb, hCb, hbridge⟩ :=
    exists_tensorPouSobolevHsNorm_toReal_le_iteratedCovGrad_tensorL2Norm_sum
      (I := I) (M := M) g 0 2 1
  obtain ⟨Cg, hCg, hHess⟩ :=
    exists_secondCovGrad_l2Norm_le_rawConnLap_add_self (I := I) (M := M) g
  refine ⟨Cb * (1 + Cg + 1), by positivity, fun T => ?_⟩
  set nLap : ℝ := ‖SmoothCcTensor.toL2 (rawTensorConnLapSmooth (I := I) g 0 2 T)‖ with hnLap_def
  set nT : ℝ := ‖SmoothCcTensor.toL2 T‖ with hnT_def
  have hnLap_nn : 0 ≤ nLap := norm_nonneg _
  have hnT_nn : 0 ≤ nT := norm_nonneg _
  -- Rewrite the abstract-`L²` norms appearing in `nLap, nT` as `tensorL2Norm … .toFun`.
  have hnLap_eq : nLap =
      tensorL2Norm (I := I) (M := M) g 0 2 (rawTensorConnLapSmooth (I := I) g 0 2 T).toFun := by
    rw [hnLap_def, SmoothCcTensor.norm_toL2,
      tensorL2Norm_toFun_eq_norm (I := I) (M := M) g
        (rawTensorConnLapSmooth (I := I) g 0 2 T)]
  have hnT_eq : nT = tensorL2Norm (I := I) (M := M) g 0 2 T.toFun := by
    rw [hnT_def, SmoothCcTensor.norm_toL2, tensorL2Norm_toFun_eq_norm (I := I) (M := M) g T]
  -- The three iterated-covGrad `L²` norms in the bridge sum (literals as the bridge produces them).
  set nGrad : ℝ := tensorL2Norm (I := I) (M := M) g 0 (2 + 1)
    (iteratedCovGrad g 0 2 1 T).toFun with hnGrad_def
  set nHess : ℝ := tensorL2Norm (I := I) (M := M) g 0 (2 + 1 + 1)
    (iteratedCovGrad g 0 2 2 T).toFun with hnHess_def
  have hnGrad_nn : 0 ≤ nGrad := tensorL2Norm_nonneg (I := I) (M := M) g 0 (2 + 1) _
  have hnHess_nn : 0 ≤ nHess := tensorL2Norm_nonneg (I := I) (M := M) g 0 (2 + 1 + 1) _
  -- The bridge sum `∑_{j ∈ range 3} ‖∇^j T‖_{L²}` is exactly `nT + nGrad + nHess`.
  have hsum_eq :
      (∑ j ∈ Finset.range (2 * 1 + 1),
        tensorL2Norm (I := I) (M := M) g 0 (2 + j)
          (iteratedCovGrad g 0 2 j T).toFun) = nT + nGrad + nHess := by
    have h2 : (2 * 1 + 1 : ℕ) = 3 := by norm_num
    rw [h2, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
      iteratedCovGrad_zero]
    rw [show tensorL2Norm (I := I) (M := M) g 0 (2 + 0) T.toFun = nT from by rw [hnT_eq]]
  have hbridge_T := hbridge T
  rw [hsum_eq] at hbridge_T
  -- `nGrad`, `nHess` as the geometric `covGrad` chains used by the order-1 / order-2 controls.
  have hnGrad_cov : nGrad =
      tensorL2Norm (I := I) (M := M) g 0 3 (covGrad (I := I) (M := M) g 0 2 T).toFun := by
    rw [hnGrad_def, iteratedCovGrad_succ, iteratedCovGrad_zero]
  have hnHess_cov : nHess =
      tensorL2Norm (I := I) (M := M) g 0 (3 + 1)
        (covGrad (I := I) (M := M) g 0 3 (covGrad (I := I) (M := M) g 0 2 T)).toFun := by
    rw [hnHess_def, iteratedCovGrad_succ, iteratedCovGrad_succ, iteratedCovGrad_zero]
  -- order-1 control `‖∇T‖² ≤ ‖Δ_∇T‖ · ‖T‖`, and the Young absorption `‖∇T‖ ≤ (nLap + nT)/2`.
  have horder1 : nGrad ^ 2 ≤
      tensorL2Norm (I := I) (M := M) g 0 2 (rawTensorConnLapSmooth (I := I) g 0 2 T).toFun *
        tensorL2Norm (I := I) (M := M) g 0 2 T.toFun := by
    rw [hnGrad_cov]
    exact covGrad_l2NormSq_le_rawConnLap_mul_self (I := I) (M := M) g T
  have horder1' : nGrad ^ 2 ≤ nLap * nT := by rw [hnLap_eq, hnT_eq]; exact horder1
  have hgrad_le : nGrad ≤ (nLap + nT) / 2 := by
    have hyoung : nLap * nT ≤ ((nLap + nT) / 2) ^ 2 := by nlinarith [sq_nonneg (nLap - nT)]
    have hgrad_sq : nGrad ^ 2 ≤ ((nLap + nT) / 2) ^ 2 := le_trans horder1' hyoung
    have hhalf_nn : 0 ≤ (nLap + nT) / 2 := by linarith
    exact le_of_sq_le_sq hgrad_sq hhalf_nn
  -- the order-2 covariant Gårding bound `‖∇²T‖ ≤ Cg · (nLap + nT)`.
  have hHess_le : nHess ≤ Cg * (nLap + nT) := by
    have := hHess T
    rw [← hnHess_cov, ← hnLap_eq, ← hnT_eq] at this
    exact this
  -- assemble: nT + nGrad + nHess ≤ (1 + Cg + 1) · (nLap + nT).
  have hsum_le : nT + nGrad + nHess ≤ (1 + Cg + 1) * (nLap + nT) := by
    have hnT_le : nT ≤ 1 * (nLap + nT) := by rw [one_mul]; linarith
    have hgrad_le' : nGrad ≤ 1 * (nLap + nT) := by
      rw [one_mul]; linarith [hgrad_le]
    nlinarith [hnT_le, hgrad_le', hHess_le, hCg, hnLap_nn, hnT_nn]
  calc (tensorPouSobolevHsNorm (I := I) (M := M) g 1 T).toReal
      ≤ Cb * (nT + nGrad + nHess) := hbridge_T
    _ ≤ Cb * ((1 + Cg + 1) * (nLap + nT)) :=
        mul_le_mul_of_nonneg_left hsum_le hCb
    _ = Cb * (1 + Cg + 1) * (nLap + nT) := by ring

set_option linter.unusedSectionVars false in
/-- **The quantitative chart-`H²` Gårding constant in the `h_elliptic` consumer shape.** There is a
nonnegative constant `C`, uniform in `T`, with
```
(tensorPouSobolevHsNorm g 1 T).toReal ≤ C · ∑_{j ∈ range 2} ‖Δ_∇^j T‖_{L²},
```
for every smooth compactly-supported `(0, 2)`-tensor field `T`. This is *exactly* the `k = 1`
instance of the elliptic hypothesis `h_elliptic` of `eigenSpan_pouHs_le_spectral_of_elliptic`
(`Analysis/Spectral/Intrinsic/Garding/EigenComboGardingReduction.lean`), the two summands being
`‖Δ_∇^0 T‖_{L²} = ‖T‖_{L²}` (`rawTensorConnLapIter_zero`) and `‖Δ_∇^1 T‖_{L²} = ‖Δ_∇ T‖_{L²}`
(`rawTensorConnLapIter_one`). It is `exists_tensorPouSobolevHsNorm_one_le_rawConnLap_add_self`
re-expressed against the `rawTensorConnLapIter` sum the consumer uses. -/
theorem exists_tensorPouSobolevHsNorm_one_le_sum_rawConnLapIter
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : SmoothCcTensor g 0 2,
        (tensorPouSobolevHsNorm (I := I) (M := M) g 1 T).toReal ≤
          C * ∑ j ∈ Finset.range (1 + 1),
            ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g 0 2 j T)‖ := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_tensorPouSobolevHsNorm_one_le_rawConnLap_add_self (I := I) (M := M) g
  refine ⟨C, hC, fun T => ?_⟩
  have hsum_eq :
      (∑ j ∈ Finset.range (1 + 1),
        ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g 0 2 j T)‖) =
      ‖SmoothCcTensor.toL2 (rawTensorConnLapSmooth (I := I) g 0 2 T)‖ +
        ‖SmoothCcTensor.toL2 T‖ := by
    rw [Finset.sum_range_succ, Finset.sum_range_one,
      rawTensorConnLapIter_zero (I := I) (M := M) g 0 2 T,
      rawTensorConnLapIter_one (I := I) (M := M) g 0 2 T]
    ring
  rw [hsum_eq]
  exact hbound T

end Connection
end Integral
end DifferentialGeometry

end
