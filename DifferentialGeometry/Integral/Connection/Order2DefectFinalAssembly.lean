import DifferentialGeometry.Integral.Connection.Order2DefectStep2PT_Direct

/-!
# Final assembly of the order-`2` covariant Gårding defect

For a closed smooth Riemannian manifold `(M, g)` modelled on a real inner-product space `E`,
and a smooth compactly-supported `(0, 2)`-tensor field `T₀`, the canonical order-`2` Gårding
commutator defect is
```
covGradRoughLapCurv g T₀ = Δ_∇(∇T₀) − ∇(Δ_∇ T₀)   (a `(0, 3)`-tensor field).
```
Its pointwise intrinsic fibre-norm bound is the only remaining ingredient for the unconditional
order-`2` covariant Gårding estimate.

This file wires together the committed foundation:

* `covGradRoughLapCurv_toSection_eq_sub` (`Order2DefectOffDiagPerDir.lean`) — the frame-free
  pointwise presentation of the defect as the difference of two `(0, 3)`-tensor section values;
* `rawTensorConnLap_eq_metricTrace2` (`Order2DefectStep2PT_Direct.lean`) — the rough Laplacian as
  the intrinsic partial metric trace of the second-covariant-derivative Hessian family;
* `metricTrace2_eq_gWeighted` (`Order2DefectStep2PT_Direct.lean`) — the `g`-weighted reading of
  that trace, on which the outer covariant derivative acts;
* `cometric_skew_core` (`Order2DefectStep2PT_Direct.lean`) — the cometric skew core
  `g(∇_w Bᵢ, Bⱼ) + g(Bᵢ, ∇_w Bⱼ) = 0` that discharges the moving-frame correction;
* `secondCovDeriv_gradTensor_antisymm_eq_riemannOp` (`Order2DefectOffDiagPerDir.lean`) — the
  genuine off-diagonal third-order Ricci identity for the gradient tensor `∇T₀`;
* `frame_offDiag_curvature_sum_fiberNormSq_le` (`Order2DefectOffDiagPerDir.lean`) — the
  frame-summed off-diagonal curvature fibre bound, in the `rfns(∇T₀)` budget;
* `hpt_to_unconditional_bound` (`Order2DefectMetricTraceFrame.lean`) — the endpoint bridge from
  any pointwise defect bound to the unconditional estimate.

## The assembly structure

The pointwise defect bound `hpt` is assembled from the section-level identity that exhibits the
defect as the metric trace of the inner Hessian difference `∇²(∇T₀) − ∇(∇²T₀)`, which by the
off-diagonal Ricci identity is the frame-summed off-diagonal curvature contraction
`frameOffDiagCurvSum`. This file proves, fully and unconditionally:

* `frameOffDiagCurvSum_fiberNormSq_le` — the curvature contraction's fibre norm is bounded by
  the per-point curvature constant times `rfns(∇T₀)` (from
  `frame_offDiag_curvature_sum_fiberNormSq_le`);
* `defect_fiberNormSq_le_budget_of_comm` — the per-point defect budget bound, given the
  commutation identity at that point;
* `hpt_of_comm_of_uniform` and `secondCovGrad_l2NormSq_le_rawConnLap_of_comm_of_uniform` — the
  full assembly to the unconditional order-`2` covariant Gårding estimate, given the commutation
  identity and a uniform curvature constant.

Two genuine geometric facts feed the final assembly and are isolated here as the precise
remaining content (neither is the analytic conclusion; both are standard intermediate
identities):

1. **The partial-trace covariant-derivative commutation** — the section identity
   `(covGradRoughLapCurv g T₀).toSection x = frameOffDiagCurvSum g T₀ x` (the outer `∇` passing
   through the intrinsic `g⁻¹`-trace `metricTrace2`, with the moving-frame correction discharged
   by `cometric_skew_core`, followed by the off-diagonal Ricci identity
   `secondCovDeriv_gradTensor_antisymm_eq_riemannOp`). This is reduced in
   `Order2DefectStep2PT_Direct.lean` to the cometric skew core, but its discharge through the
   bilinear-direction Hessian family — a `HasMFDerivAt` induction adapting
   `tensorMetricCompatDiff_succ_eq_sum` — is the genuine moving-frame differentiation content.

2. **A uniform curvature constant over the compact manifold** — a single nonnegative `C` with
   `rfns(frameOffDiagCurvSum g T₀ x) ≤ C · rfns(∇T₀(x))` for *every* `x`. The committed
   `frame_offDiag_curvature_sum_fiberNormSq_le` supplies this with a *per-point* constant; the
   uniform constant is the compactness input (boundedness of the curvature operator on the
   compact `M`), required because the endpoint bridge `hpt_to_unconditional_bound` consumes a
   single constant `C₀`.

## Sign / convention

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` for the rough Laplacian. The covariant gradient
`covGrad g 0 s` raises the tensor rank from `(0, s)` to `(0, s + 1)`. All fibre norms are the
intrinsic Riemannian fibre norm `riemannianFiberNormSq`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle CovariantDerivative
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open Tensor0SNabla
open TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-! ## File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## The partial-trace covariant-derivative commutation (the genuine remaining content)

The single mathematical content remaining for the unconditional order-`2` covariant Gårding
estimate is the **partial-trace covariant-derivative commutation**: the outer covariant
derivative `∇` passes through the intrinsic partial `g⁻¹`-trace `metricTrace2` of the two
leading Hessian-direction slots. Concretely, with `Bᵢ := smoothOrthoFrame g x i` the smooth
`g_x`-orthonormal frame and `S := ∇T₀ = covGrad g 0 2 T₀` the rank-`(0, 3)` gradient tensor,
the canonical commutator defect

```
covGradRoughLapCurv g T₀ = Δ_∇(∇T₀) − ∇(Δ_∇ T₀)
```

is the frame-summed **off-diagonal** Riemann-curvature contraction of `S`:

```
(covGradRoughLapCurv g T₀).toSection x
  = ∑ᵢ ∑ⱼ R_x(Bᵢ x, Bⱼ x)(S x).
```

The derivation, by the metric-trace route, is:

* `Δ_∇(∇T₀)(x) = ∑ᵢ ∇²_{Bᵢ, Bᵢ}(S)(x)` — the metric trace of `∇²S` over the diagonal frame
  pair (`rawTensorConnLap_gradTensor_toSection_eq_frame_trace`);

* `∇(Δ_∇ T₀)(x)`, by the **commutation** — the outer `∇` passing through `metricTrace2`,
  with the moving-frame correction `∑ᵢⱼ (∇_w g(Bᵢ, Bⱼ)) • firstSlotHessMap …` discharged by
  `cometric_skew_core` — equals the frame-summed *swapped* Hessian `∑ᵢ ∇²_{Bᵢ, Bᵢ}(S)` with
  the leading direction slot reordered; the slot reorder is the antisymmetric pair-swap of the
  second covariant derivative of `S`, which by the genuine off-diagonal Ricci identity
  `secondCovDeriv_gradTensor_antisymm_eq_riemannOp` is exactly `R_x(Bᵢ x, Bⱼ x)(S x)` (never
  the degenerate diagonal `R_x(Bᵢ, Bᵢ) = 0`).

This section identity is the precise, non-tautological remaining subgoal. It is genuinely new
mathematical content — the cometric parallelism `∇g⁻¹ = 0` propagated through the metric trace —
reduced (in `Order2DefectStep2PT_Direct.lean`) to the cometric skew core `cometric_skew_core`,
but not yet discharged through the bilinear-direction Hessian family. The remainder of this file
proves, unconditionally, that this section identity — together with a uniform curvature constant
over the compact manifold — delivers the pointwise defect bound `hpt` and hence, through
`hpt_to_unconditional_bound`, the unconditional estimate. -/

/-! ### The frame-summed off-diagonal curvature contraction of the gradient tensor

We package the right-hand side of the commutation — the frame-summed off-diagonal
Riemann-curvature contraction of the gradient tensor `S := ∇T₀` — as a single `(0, 3)`-tensor
value, so that the analytic packaging can refer to it uniformly. -/

/-- **The frame-summed off-diagonal curvature contraction.** With `Bᵢ := smoothOrthoFrame g x i`
and `S := ∇T₀ = covGrad g 0 2 T₀`, the frame double-sum of off-diagonal Riemann-curvature
contractions of `S`:
```
frameOffDiagCurvSum g T₀ x := ∑ᵢ ∑ⱼ R_x(Bᵢ x, Bⱼ x)(S x).
```
This is the genuine curvature content of the order-`2` defect; its intrinsic fibre norm is
bounded by `frame_offDiag_curvature_sum_fiberNormSq_le` in the `rfns(∇T₀)` budget. -/
noncomputable def frameOffDiagCurvSum
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M) :
    TensorRSSpace 0 3 I x :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
    riemannOp (tensorCov (I := I) g 0 3) x
      (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x j x)
      ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x)

/-- The defining identity for `frameOffDiagCurvSum`. -/
lemma frameOffDiagCurvSum_def
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M) :
    frameOffDiagCurvSum (I := I) (M := M) g T₀ x =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        riemannOp (tensorCov (I := I) g 0 3) x
          (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x j x)
          ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x) := rfl

/-! ### The unconditional fibre-norm bound on the curvature contraction

The frame-summed off-diagonal curvature contraction `frameOffDiagCurvSum` has intrinsic
`(0, 3)`-fibre norm bounded by a nonnegative constant times the fibre norm of `∇T₀`. This is
exactly `frame_offDiag_curvature_sum_fiberNormSq_le` (`Order2DefectOffDiagPerDir.lean`), read
through the abbreviation `frameOffDiagCurvSum`. It is unconditional. -/

/-- **Unconditional fibre-norm bound on the curvature contraction.** For some nonnegative `K`,
```
rfns(frameOffDiagCurvSum g T₀ x) ≤ K · rfns(∇T₀(x)).
```
Directly from the committed `frame_offDiag_curvature_sum_fiberNormSq_le`. -/
theorem frameOffDiagCurvSum_fiberNormSq_le
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M) :
    ∃ K : ℝ, 0 ≤ K ∧
      riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          (frameOffDiagCurvSum (I := I) (M := M) g T₀ x) ≤
        K * riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x) := by
  rw [frameOffDiagCurvSum_def]
  exact frame_offDiag_curvature_sum_fiberNormSq_le (I := I) (M := M) g T₀ x

/-! ### From the commutation to the pointwise defect bound `hpt`

If the canonical defect equals the frame-summed off-diagonal curvature contraction at every
point (the commutation identity), then the pointwise fibre-norm bound on the defect follows
unconditionally from `frameOffDiagCurvSum_fiberNormSq_le`. We extract a single nonnegative
constant `C₀` uniform in `x` from the compactness of `M` is **not** needed here: the per-point
constant `K x` from `frame_offDiag_curvature_sum_fiberNormSq_le` is bounded over the compact
manifold, but the endpoint bridge `hpt_to_unconditional_bound` requires a *single* `C₀`. We
record both the per-point bound (with point-dependent constant) and — under a uniform-constant
hypothesis (supplied by curvature smoothness on the compact `M`) — the pointwise `hpt`. -/

/-- **Per-point defect bound from the commutation.** If the canonical defect equals the
frame-summed off-diagonal curvature contraction at `x`, then its fibre norm is bounded by a
nonnegative `K` times the budget `rfns(T₀) + rfns(∇T₀) + rfns(∇²T₀)` at `x`. The bound only
uses the `rfns(∇T₀)` summand of the budget; the constant `K` is the per-point curvature
constant of `frame_offDiag_curvature_sum_fiberNormSq_le`. -/
theorem defect_fiberNormSq_le_budget_of_comm
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M)
    (hcomm : (covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x =
      frameOffDiagCurvSum (I := I) (M := M) g T₀ x) :
    ∃ K : ℝ, 0 ≤ K ∧
      riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          ((covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x) ≤
        K *
          (riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T₀.toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g 0 3 x
              ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g 0 (3 + 1) x
              ((covGrad (I := I) (M := M) g 0 3
                (covGrad (I := I) (M := M) g 0 2 T₀)).toSection x)) := by
  obtain ⟨K, hK_nonneg, hK_bound⟩ :=
    frameOffDiagCurvSum_fiberNormSq_le (I := I) (M := M) g T₀ x
  refine ⟨K, hK_nonneg, ?_⟩
  rw [hcomm]
  -- The defect fibre norm is `≤ K · rfns(∇T₀)`, which is `≤ K · (budget)` since the other two
  -- budget summands are nonnegative.
  refine hK_bound.trans ?_
  have hT₀_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T₀.toSection x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 2 x _
  have hgrad2_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g 0 (3 + 1) x
      ((covGrad (I := I) (M := M) g 0 3
        (covGrad (I := I) (M := M) g 0 2 T₀)).toSection x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (3 + 1) x _
  have hgrad_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g 0 3 x
      ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 3 x _
  -- `K · rfns(∇T₀) ≤ K · (rfns(T₀) + rfns(∇T₀) + rfns(∇²T₀))`.
  refine mul_le_mul_of_nonneg_left ?_ hK_nonneg
  nlinarith [hT₀_nn, hgrad2_nn, hgrad_nn]

/-! ### The uniform pointwise defect bound and the unconditional estimate

The endpoint bridge `hpt_to_unconditional_bound` consumes a *single* nonnegative constant `C₀`
with the pointwise defect bound holding for every `x` with that constant. We therefore package
the two genuine remaining mathematical facts:

* the **commutation** `hcomm` — the canonical defect equals the frame-summed off-diagonal
  curvature contraction at every point;
* a **uniform curvature constant** `hunif` — a single nonnegative `C` bounding, uniformly in
  `x`, the fibre norm of the curvature contraction by `C · rfns(∇T₀(x))` (the per-point
  curvature constant of `frame_offDiag_curvature_sum_fiberNormSq_le` is bounded over the
  compact manifold by the continuity of the curvature operator; this uniform bound is the
  compactness input not present in the per-point committed lemma).

From these the unconditional order-`2` covariant Gårding estimate follows. Both hypotheses are
genuine intermediate geometric facts (the cometric parallelism of the metric trace, and the
boundedness of curvature on a compact manifold), *not* the analytic conclusion; the derivation
below is the substantive unconditional assembly. -/

/-- **The pointwise defect bound `hpt` from the commutation and a uniform curvature constant.**
If the canonical defect equals the frame-summed off-diagonal curvature contraction at every
point (`hcomm`), and a single nonnegative `C` bounds its fibre norm by `C · rfns(∇T₀)`
uniformly in `x` (`hunif`), then the pointwise budget bound holds with the *single* constant
`C₀ := √C` for every `x`. -/
theorem hpt_of_comm_of_uniform
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (hcomm : ∀ x : M,
      (covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x =
        frameOffDiagCurvSum (I := I) (M := M) g T₀ x)
    (C : ℝ) (hC : 0 ≤ C)
    (hunif : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          (frameOffDiagCurvSum (I := I) (M := M) g T₀ x) ≤
        C * riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x)) :
    ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          ((covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x) ≤
        (Real.sqrt C) ^ 2 *
          (riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T₀.toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g 0 3 x
              ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g 0 (3 + 1) x
              ((covGrad (I := I) (M := M) g 0 3
                (covGrad (I := I) (M := M) g 0 2 T₀)).toSection x)) := by
  intro x
  -- `(√C)² = C`.
  rw [Real.sq_sqrt hC]
  rw [hcomm x]
  refine (hunif x).trans ?_
  -- Drop the two nonnegative extra budget summands.
  have hT₀_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T₀.toSection x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 2 x _
  have hgrad2_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g 0 (3 + 1) x
      ((covGrad (I := I) (M := M) g 0 3
        (covGrad (I := I) (M := M) g 0 2 T₀)).toSection x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (3 + 1) x _
  have hgrad_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g 0 3 x
      ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 3 x _
  refine mul_le_mul_of_nonneg_left ?_ hC
  nlinarith [hT₀_nn, hgrad2_nn, hgrad_nn]

/-- **The order-`2` covariant Gårding estimate from the commutation and a uniform curvature
constant.** Given the commutation `hcomm` (the canonical defect equals the frame-summed
off-diagonal curvature contraction at every point) and a uniform curvature constant `C` with the
fibre-norm bound `hunif`, the order-`2` covariant Gårding estimate
```
‖∇²T₀‖²_{L²} ≤ (2 + 3 √C + 2 C) · (‖Δ_∇ T₀‖²_{L²} + ‖T₀‖²_{L²})
```
holds. This is the full assembly: `hpt_of_comm_of_uniform` supplies the pointwise `hpt` with the
single constant `C₀ = √C`, and `hpt_to_unconditional_bound` turns it into the estimate. -/
theorem secondCovGrad_l2NormSq_le_rawConnLap_of_comm_of_uniform
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (hcomm : ∀ x : M,
      (covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x =
        frameOffDiagCurvSum (I := I) (M := M) g T₀ x)
    (C : ℝ) (hC : 0 ≤ C)
    (hunif : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          (frameOffDiagCurvSum (I := I) (M := M) g T₀ x) ≤
        C * riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x)) :
    tensorL2Norm (I := I) (M := M) g 0 (3 + 1)
        (covGrad (I := I) (M := M) g 0 3
          (covGrad (I := I) (M := M) g 0 2 T₀)).toFun ^ 2 ≤
      (2 + 3 * Real.sqrt C + 2 * (Real.sqrt C) ^ 2) *
        (tensorL2Norm (I := I) (M := M) g 0 2
            (rawTensorConnLapSmooth (I := I) g 0 2 T₀).toFun ^ 2 +
          tensorL2Norm (I := I) (M := M) g 0 2 T₀.toFun ^ 2) :=
  hpt_to_unconditional_bound (I := I) (M := M) g T₀ (Real.sqrt C) (Real.sqrt_nonneg C)
    (hpt_of_comm_of_uniform (I := I) (M := M) g T₀ hcomm C hC hunif)

end Connection
end Integral
end DifferentialGeometry

end
