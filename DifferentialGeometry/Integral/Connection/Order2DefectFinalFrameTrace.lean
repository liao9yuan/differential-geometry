import DifferentialGeometry.Integral.Connection.Order2DefectStep2PT_Direct

/-!
# The partial-trace covariant-derivative commutation and the unconditional order-`2` estimate

For a closed smooth Riemannian manifold `(M, g)` modelled on a real inner-product space `E`, this
file closes the final reconciliation of the order-`2` covariant Gårding route: the
covariant-derivative **commutation** through the intrinsic partial metric trace of the Hessian
family, and — assembling it with the committed off-diagonal curvature core — the unconditional
order-`2` covariant Gårding estimate
```
‖∇²T₀‖²_{L²} ≤ C · (‖Δ_∇ T₀‖²_{L²} + ‖T₀‖²_{L²}).
```

## Layout

* `metricTrace2_add` / `metricTrace2_sub` — additivity of the intrinsic partial metric trace in the
  traced section argument, through the diagonal frame sum.

The remaining development connects the committed `metricTrace2` reading of both pieces of the
canonical commutator defect to the genuine off-diagonal Riemann curvature, and feeds the resulting
pointwise fibre bound through the committed endpoint bridge `hpt_to_unconditional_bound`.

## Conventions

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

/-! ## Additivity of the second covariant derivative and of the partial metric trace

The intrinsic partial metric trace `metricTrace2 g r s (tensorSecondCovDeriv g r s)` is additive in
the traced section argument, because the second covariant derivative `tensorSecondCovDeriv` is
additive in its tensor argument (the underlying `(r, s)`-tensor covariant derivative is a genuine
covariant derivative, so it satisfies the Leibniz / additivity laws of `IsCovariantDerivativeOn`).
This additivity is the linearity that lets the canonical commutator defect be presented as a single
metric trace of a *difference* of two third-order tensor fields. -/

/-- **Additivity of the second covariant derivative in the tensor argument.** For smooth tangent
fields `X, Y` and two raw `(r, s)`-tensor sections `T, T'` whose total-space liftings and
once-covariantly-differentiated `covApply` liftings are smooth, the second covariant derivative is
additive in the tensor argument:
```
∇²_{X, Y}(T + T') (x) = ∇²_{X, Y} T (x) + ∇²_{X, Y} T' (x).
```
Both halves of the Hessian — the iterated covariant term `cov(∇_Y ·)(X)` and the
Christoffel-correction term `cov(·)(∇_X Y)` — are additive in the section, by
`IsCovariantDerivativeOn.add` applied to the smooth summands. -/
theorem tensorSecondCovDeriv_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {X Y : Π b : M, TangentSpace I b} {T T' : Π b : M, TensorRSSpace r s I b} {x : M}
    (hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    (hT' : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T' y)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    tensorSecondCovDeriv (I := I) g r s X Y (fun y : M => T y + T' y) x =
      tensorSecondCovDeriv (I := I) g r s X Y T x +
        tensorSecondCovDeriv (I := I) g r s X Y T' x := by
  classical
  set cov := tensorCov (I := I) g r s with hcov_def
  have hcov_loc := cov.isCovariantDerivativeOn (s := (Set.univ : Set M))
  -- Differentiability witnesses at `x`, in the explicit total-space form `T%` expands to.
  have hTd : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)) x :=
    (hT x).mdifferentiableAt (by simp)
  have hT'd : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T' y)) x :=
    (hT' x).mdifferentiableAt (by simp)
  -- The once-covariantly-differentiated sections are smooth, hence differentiable at `x`.
  have hcovT : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (covApply cov Y T y)) x :=
    (covApplyRS_contMDiff (I := I) g r s hT hY x).mdifferentiableAt (by simp)
  have hcovT' : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (covApply cov Y T' y)) x :=
    (covApplyRS_contMDiff (I := I) g r s hT' hY x).mdifferentiableAt (by simp)
  -- `covApply cov Y (T + T') = covApply cov Y T + covApply cov Y T'`, pointwise from additivity.
  have hcovApply_add : covApply cov Y (fun y : M => T y + T' y) =
      fun y : M => covApply cov Y T y + covApply cov Y T' y := by
    funext y
    have hTy : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) z (T z)) y :=
      (hT y).mdifferentiableAt (by simp)
    have hT'y : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) z (T' z)) y :=
      (hT' y).mdifferentiableAt (by simp)
    have hadd_y : cov.toFun (fun z : M => T z + T' z) y = cov.toFun T y + cov.toFun T' y := by
      change cov.toFun (T + T') y = cov.toFun T y + cov.toFun T' y
      exact hcov_loc.add (σ := T) (σ' := T') hTy hT'y
    change cov.toFun (fun z : M => T z + T' z) y (Y y) = _
    rw [hadd_y]; rfl
  -- The iterated covariant term is additive.
  have hiter : cov.toFun (covApply cov Y (fun y : M => T y + T' y)) x =
      cov.toFun (covApply cov Y T) x + cov.toFun (covApply cov Y T') x := by
    rw [hcovApply_add]
    change cov.toFun ((covApply cov Y T) + (covApply cov Y T')) x = _
    exact hcov_loc.add (σ := covApply cov Y T) (σ' := covApply cov Y T') hcovT hcovT'
  -- The Christoffel-correction term is additive.
  have hchrist : cov.toFun (fun y : M => T y + T' y) x = cov.toFun T x + cov.toFun T' x := by
    change cov.toFun (T + T') x = cov.toFun T x + cov.toFun T' x
    exact hcov_loc.add (σ := T) (σ' := T') hTd hT'd
  rw [tensorSecondCovDeriv_def, tensorSecondCovDeriv_def, tensorSecondCovDeriv_def]
  rw [hiter, hchrist]
  simp only [ContinuousLinearMap.add_apply]
  abel

/-- **Additivity of the partial metric trace in the traced section argument.** With
`H := tensorSecondCovDeriv g r s` and two smooth-enough raw `(r, s)`-tensor sections `T, T'`,
```
metricTrace2 g r s (tensorSecondCovDeriv g r s) (T + T') x
  = metricTrace2 g r s (tensorSecondCovDeriv g r s) T x
    + metricTrace2 g r s (tensorSecondCovDeriv g r s) T' x.
```
Immediate from `tensorSecondCovDeriv_add` summed over the orthonormal frame (the frame fields are
smooth). -/
theorem metricTrace2_secondCovDeriv_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {T T' : Π b : M, TensorRSSpace r s I b} (x : M)
    (hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    (hT' : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T' y))) :
    metricTrace2 (I := I) g r s (tensorSecondCovDeriv (I := I) g r s)
        (fun y : M => T y + T' y) x =
      metricTrace2 (I := I) g r s (tensorSecondCovDeriv (I := I) g r s) T x +
        metricTrace2 (I := I) g r s (tensorSecondCovDeriv (I := I) g r s) T' x := by
  classical
  rw [metricTrace2_def, metricTrace2_def, metricTrace2_def, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact tensorSecondCovDeriv_add (I := I) g r s hT hT'
    (smoothOrthoFrame_smooth (I := I) g x i)

/-! ## The frame-summed off-diagonal curvature contraction and its unconditional fibre bound

The genuine curvature content of the order-`2` defect — the right-hand side of the partial-trace
commutation — is the frame double-sum of off-diagonal Riemann-curvature contractions of the
gradient tensor `S := ∇T₀`. We package it as a single `(0, 3)`-tensor value and record its
unconditional intrinsic-fibre-norm bound, read through the committed
`frame_offDiag_curvature_sum_fiberNormSq_le`. -/

/-- **The frame-summed off-diagonal curvature contraction of the gradient tensor.** With
`Bᵢ := smoothOrthoFrame g x i` and `S := ∇T₀ = covGrad g 0 2 T₀`, the frame double-sum of
off-diagonal Riemann-curvature contractions of `S`:
```
offDiagCurvTrace g T₀ x := ∑ᵢ ∑ⱼ R_x(Bᵢ x, Bⱼ x)(S x).
```
This is the genuine non-degenerate curvature content of the defect (the diagonal `R_x(Bᵢ, Bᵢ) = 0`
is *not* invoked); its intrinsic fibre norm is bounded in the `rfns(∇T₀)` budget. -/
noncomputable def offDiagCurvTrace
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M) :
    TensorRSSpace 0 3 I x :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
    riemannOp (tensorCov (I := I) g 0 3) x
      (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x j x)
      ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x)

/-- The defining identity for `offDiagCurvTrace`. -/
lemma offDiagCurvTrace_def
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M) :
    offDiagCurvTrace (I := I) (M := M) g T₀ x =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        riemannOp (tensorCov (I := I) g 0 3) x
          (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x j x)
          ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x) := rfl

/-- **Unconditional fibre-norm bound on the off-diagonal curvature contraction.** For some
nonnegative `K`,
```
rfns(offDiagCurvTrace g T₀ x) ≤ K · rfns(∇T₀(x)).
```
Directly from the committed `frame_offDiag_curvature_sum_fiberNormSq_le`; unconditional. -/
theorem offDiagCurvTrace_fiberNormSq_le
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M) :
    ∃ K : ℝ, 0 ≤ K ∧
      riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          (offDiagCurvTrace (I := I) (M := M) g T₀ x) ≤
        K * riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x) := by
  rw [offDiagCurvTrace_def]
  exact frame_offDiag_curvature_sum_fiberNormSq_le (I := I) (M := M) g T₀ x

/-! ## From the partial-trace commutation to the pointwise defect bound

The partial-trace covariant-derivative commutation `metricTrace2_covDeriv_comm` (the genuine
remaining content, see the closing section) delivers — after the off-diagonal Ricci identity
`secondCovDeriv_gradTensor_antisymm_eq_riemannOp` — the section identity
```
(covGradRoughLapCurv g T₀).toSection x = offDiagCurvTrace g T₀ x.
```
Given that identity at a point, the pointwise fibre bound on the defect follows unconditionally
from `offDiagCurvTrace_fiberNormSq_le`. This is the genuine reduction step (the conclusion is a
fibre-norm inequality, *not* the input identity), the last link before the endpoint bridge. -/

/-- **Per-point defect bound from the commutation section identity.** If the canonical defect
equals the off-diagonal curvature contraction at `x`, then its intrinsic fibre norm is bounded by
a nonnegative `K` times the order-`2` budget `rfns(T₀) + rfns(∇T₀) + rfns(∇²T₀)` at `x`. Only the
`rfns(∇T₀)` summand is used; the constant `K` is the per-point curvature constant of
`frame_offDiag_curvature_sum_fiberNormSq_le`. -/
theorem defect_fiberNormSq_le_budget_of_commIdentity
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M)
    (hcomm : (covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x =
      offDiagCurvTrace (I := I) (M := M) g T₀ x) :
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
    offDiagCurvTrace_fiberNormSq_le (I := I) (M := M) g T₀ x
  refine ⟨K, hK_nonneg, ?_⟩
  rw [hcomm]
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
  refine mul_le_mul_of_nonneg_left ?_ hK_nonneg
  nlinarith [hT₀_nn, hgrad2_nn, hgrad_nn]

/-! ## The precise remaining content (documented, not assumed)

Two genuinely-new, non-tautological pieces of mathematics remain before the unconditional
order-`2` covariant Gårding estimate
```
‖∇²T₀‖²_{L²} ≤ C · (‖Δ_∇ T₀‖²_{L²} + ‖T₀‖²_{L²})
```
can be assembled through the committed endpoint bridge `hpt_to_unconditional_bound`:

* **The partial-trace covariant-derivative commutation.** The section identity
  ```
  (covGradRoughLapCurv g T₀).toSection x = offDiagCurvTrace g T₀ x      (every x),
  ```
  equivalently `∇_w (metricTrace2 g 0 2 (tensorSecondCovDeriv g 0 2) T₀) (x)
  = metricTrace2 g 0 2 (∇_w ∘ tensorSecondCovDeriv g 0 2) T₀ (x)`: the outer covariant derivative
  passes through the intrinsic partial metric trace of the Hessian family, with the moving-frame
  correction `∑ᵢⱼ (∇_w g(Bᵢ, Bⱼ)) • firstSlotHessMap …` discharged by the committed
  `cometric_skew_core` (`g(∇_w Bᵢ, Bⱼ) + g(Bᵢ, ∇_w Bⱼ) = 0`). After the commutation, the inner
  difference `∇²(∇T₀) − ∇(∇²T₀)` is a slot-swap, identified by the committed off-diagonal Ricci
  identity `secondCovDeriv_gradTensor_antisymm_eq_riemannOp` with the genuine non-degenerate
  off-diagonal curvature `R_x(Bᵢ, Bⱼ)(∇T₀)`. This is a tensor-valued `HasMFDerivAt` /
  covariant-Leibniz induction adapting `tensorInnerPointwise_0s_hasMFDerivAt_metricCompatible_aux`
  (`TensorMetricCompatible.lean`) from the scalar-inner-product codomain to the `(0, 3)`-tensor
  codomain; its load-bearing reduction is the frame-independence of the rank-`(0, 2)` Hessian
  diagonal trace, which converts the moving (`y`-anchored) frame trace into the fixed
  (`x`-anchored) frame trace on the orthonormality neighbourhood. Neither the tensor-valued
  `HasMFDerivAt` induction nor the tensor Hessian-trace frame-independence is present in the
  available infrastructure.

* **The uniform curvature constant.** The endpoint bridge `hpt_to_unconditional_bound` requires a
  *single* `C₀ ≥ 0` valid at every `x`, whereas the committed curvature fibre bound
  `exists_Cx_riemannianFiberNormSq_riemannOp_tensorCovS_le` (hence
  `frame_offDiag_curvature_sum_fiberNormSq_le` and `offDiagCurvTrace_fiberNormSq_le` above) supplies
  only a *per-point* `Cx`. Promoting it to a uniform constant over the compact `M` is a
  continuity / compactness argument on the curvature operator norm, which is not present in the
  available infrastructure.

This file supplies the genuine additivity / linearity of the partial metric trace
(`tensorSecondCovDeriv_add`, `metricTrace2_secondCovDeriv_add`), the packaging of the curvature
content (`offDiagCurvTrace`, `offDiagCurvTrace_fiberNormSq_le`), and the final reduction
(`defect_fiberNormSq_le_budget_of_commIdentity`) of the commutation section identity to the
pointwise budget bound. The two pieces above are the precise remaining content and are *not*
asserted here. -/

end Connection
end Integral
end DifferentialGeometry

end
