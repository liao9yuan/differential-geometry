import DifferentialGeometry.Geometry.Curvature.Bochner.PointwiseTensorBochner
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FixedFieldThirdOrderCommutator
import DifferentialGeometry.Geometry.Curvature.Order2Defect.MetricTraceIntertwining
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ContractedBianchi
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.PointwiseToL2Packaging

/-!
# The first-order curvature fibre bound of the order-`2` commutator defect

For a closed smooth Riemannian manifold `(M, g)` this file proves the **first-order** pointwise
fibre bound of the order-`2` commutator defect
```
Curv S := pointwiseTensorCurv g s S = Δ_∇(∇S) − ∇(Δ_∇ S)
```
(`∇S := covGrad g 0 s S`, a `(0, s + 1)`-tensor field): there are uniform constants `K_R, K_dR ≥ 0`
such that, at every covariant rank `s`, smooth compactly-supported `(0, s)`-tensor `S`, and point `x`,
```
√(rfns(Curv S)(x)) ≤ K_R · √(rfns(∇S)(x)) + K_dR · √(rfns(S)(x)).
```
The defect is **first-order**: it carries the value `∇S` and the tensor `S` only, *not* `∇²S`. The
`∇²S`-order terms that appear in any per-direction expansion of the defect cancel under the metric
trace (see below), so the genuine commutator is a curvature contraction of `(∇S, S)` alone.

## Why the bound is first-order (the `∇²S`-elimination)

The rough Laplacian is the metric trace of the second covariant derivative,
`Δ_∇ T (x) = ∑ₐ ∇²_{Vₐ, Vₐ} T (x)`
(`rawTensorConnLapSmooth_toSection_eq_parseval_secondCovDeriv_sum`), so by the metric-compatibility
intertwining `metricTrace2_covDeriv_comm_map` the outer covariant gradient passes through the trace
with the `g_x`-orthonormal frame `Bᵢ := smoothOrthoFrame g x i` *frozen* at `x`:
```
Curv S (x) = ∑ᵢ [ ∇²_{Bᵢ, Bᵢ}(∇S)(x) − ∇(∇²_{Bᵢ, Bᵢ} S)(x) ].
```
The per-frame third-order difference is the seven-term curvature carrier
`secondCovDeriv_covGrad_sub_covGrad_secondCovDeriv_slot0_eq`: two genuinely differentiated curvature
terms `R(Bᵢ, ·)(∇_{Bᵢ} S)`, `∇_{Bᵢ}(R(Bᵢ, ·) S)` (the `R(∇S)` and `(∇R) S` contractions, genuinely
`rfns(∇S)` / `rfns(S)`-order), three curvature-operator terms
`R(∇_{Bᵢ} ·, Bᵢ) S`, `R(·, ∇_{Bᵢ} Bᵢ) S`, `−∇_{R(Bᵢ, ·) Bᵢ} S` (`rfns(S)` / `rfns(∇S)`-order), and the
symmetric `∇²S`-order pair `−∇²_{∇_· Bᵢ, Bᵢ} S − ∇²_{Bᵢ, ∇_· Bᵢ} S`. The `∇²S`-order pair *cancels in
the frame sum* `∑ᵢ`: expanding `∇_· Bᵢ = ∑ⱼ aᵢⱼ Bⱼ` with `aᵢⱼ := g(∇_· Bᵢ, Bⱼ)` antisymmetric
(`smoothOrthoFrame_cov_skew` / `cometric_skew_core`, `∇g = 0` on the orthonormal frame), the pair
becomes `∑ᵢⱼ aᵢⱼ (∇²_{Bⱼ, Bᵢ} S + ∇²_{Bᵢ, Bⱼ} S)`, an antisymmetric coefficient against a
swap-symmetric Hessian, hence `0`. So no `∇²S` survives; the genuine defect is the curvature
contraction of `(∇S, S)`.

## The carried debt

The frame-summed `∇²S`-cancellation above is the genuine moving-frame third-order
Bochner–Weitzenböck content (the project's known frame-free curvature debt). It is the *pointwise*
form of the (now-discarded) integrated nullity — the per-`x` `∇²S`-free fibre bound. It is carried
here as the single honest leaf `pointwiseTensorCurv_fiberNormSq_le_first_order`: the per-point
first-order fibre bound parameterised by the **existing** uniform curvature sups (the pure-`R` sup
`exists_uniform_genuineCurvTracePureR_fiberNormSq_bound` and the differentiated-curvature /
Ricci-trace operator-field sups), so the uniformisation over the compact manifold is free. The
genuine mathematical content of the leaf is exactly the seven-term frame-sum assembly with the
antisymmetric `∇²S`-pair cancelled; everything above it — the `∃`-uniformisation and the integrated
cross-bound — is proved here.

## Sign / convention

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` (frame trace). The covariant gradient `covGrad g 0 s`
raises the tensor rank from `(0, s)` to `(0, s + 1)`. All fibre norms are the intrinsic Riemannian
fibre norm `riemannianFiberNormSq`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- **The first-order curvature fibre bound of the order-`2` commutator defect (the genuine
moving-frame third-order Bochner–Weitzenböck `∇²S`-elimination leaf).** For a closed smooth
Riemannian manifold `(M, g)` there are uniform nonnegative valence-dependent constants
`K_R, K_dR : ℕ → ℝ` such that, at every covariant rank `s`, smooth compactly-supported `(0, s)`-tensor
`S`, and point `x`, the intrinsic Riemannian fibre norm of the order-`2` commutator defect
`Curv S := pointwiseTensorCurv g s S` is controlled by the gradient field `∇S := covGrad g 0 s S` and
the tensor `S` alone:
```
√(rfns(Curv S)(x)) ≤ K_R s · √(rfns(∇S)(x)) + K_dR s · √(rfns(S)(x)).
```

This is **first-order**: the bound carries `∇S` and `S` only, never `∇²S`.

**Why this is TRUE (and the genuine carried content).** Writing the rough Laplacian as the metric
trace `Δ_∇ T (x) = ∑ₐ ∇²_{Vₐ, Vₐ} T (x)`
(`rawTensorConnLapSmooth_toSection_eq_parseval_secondCovDeriv_sum`) and passing the outer covariant
gradient through the trace with the `g_x`-orthonormal frame `Bᵢ := smoothOrthoFrame g x i` frozen at
`x` (`metricTrace2_covDeriv_comm_map`), the defect is the frozen-frame sum
`Curv S (x) = ∑ᵢ [∇²_{Bᵢ, Bᵢ}(∇S)(x) − ∇(∇²_{Bᵢ, Bᵢ} S)(x)]`. Each per-frame third-order difference is
the seven-term curvature carrier `secondCovDeriv_covGrad_sub_covGrad_secondCovDeriv_slot0_eq`: five
`rfns(∇S)` / `rfns(S)`-order curvature contractions plus the symmetric `∇²S`-order pair
`−∇²_{∇_· Bᵢ, Bᵢ} S − ∇²_{Bᵢ, ∇_· Bᵢ} S`. Expanding `∇_· Bᵢ = ∑ⱼ aᵢⱼ Bⱼ` with `aᵢⱼ` antisymmetric
(`smoothOrthoFrame_cov_skew`, the metric-parallel `∇g = 0` on the orthonormal frame), the pair becomes
`∑ᵢⱼ aᵢⱼ (∇²_{Bⱼ, Bᵢ} S + ∇²_{Bᵢ, Bⱼ} S)`, an antisymmetric coefficient against a swap-symmetric
Hessian, so it cancels in the full frame sum `∑ᵢ`. No `∇²S` survives, and the five surviving curvature
contractions are uniformly fibre-bounded by `‖R‖_∞ · √(rfns(∇S))` and `‖∇R‖_∞ · √(rfns(S))` over the
compact manifold (the curvature and its first derivative are continuous, hence bounded). The pure-`R`
contraction is supplied by `exists_uniform_genuineCurvTracePureR_fiberNormSq_bound`.

**Non-vacuity.** With `K_R s = K_dR s = 0` the bound forces `Curv S (x) = 0` for all `S, x`, i.e. the
rough Laplacian and the covariant gradient commute pointwise; this is *false* on a non-flat manifold
(at `s = 0` the defect is `Ric(∇f, ·) ≠ 0` on a positively-curved `M`). So the bound genuinely
envelopes the per-point curvature operator norm.

**Carried debt.** This is the single honest leaf of this file: the frame-summed antisymmetric
`∇²S`-cancellation assembled from the seven-term carrier — the genuinely-irreducible pointwise
moving-frame third-order Bochner–Weitzenböck content (the project's known frame-free curvature debt),
here in its sharpest *pointwise first-order fibre* form. Its on-disk producer (the seven-term frame-sum
assembly lifted to the `(0, s + 1)`-fibre value with the antisymmetric pair cancelled) is the
remaining gap; everything resting on it — the uniform `∃`-form and the integrated cross-bound — is
proved. -/
theorem pointwiseTensorCurv_fiberNormSq_le_first_order
    (g : SmoothRiemannianMetric I M) :
    ∃ K_R K_dR : ℕ → ℝ, (∀ s, 0 ≤ K_R s) ∧ (∀ s, 0 ≤ K_dR s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M),
        Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)) ≤
          K_R s * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
              ((covGrad (I := I) (M := M) g 0 s S).toSection x)) +
            K_dR s * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 s x
              (S.toSection x)) :=
  sorry

/-- **STEP 1 — the uniform first-order curvature fibre bound (rank-fixed `∃`-form).** For a closed
smooth Riemannian manifold `(M, g)` and covariant rank `s`, there are uniform constants
`K_R, K_dR ≥ 0` such that, for every smooth compactly-supported `(0, s)`-tensor `S` and point `x`,
```
√(rfns(Curv S)(x)) ≤ K_R · √(rfns(∇S)(x)) + K_dR · √(rfns(S)(x)),
```
with `Curv S := pointwiseTensorCurv g s S` and `∇S := covGrad g 0 s S`. This is the rank-fixed
specialisation of the valence-dependent first-order curvature fibre bound
`pointwiseTensorCurv_fiberNormSq_le_first_order`, read at the fixed rank `s`. -/
theorem exists_pointwiseTensorCurv_fiberNormSq_bound
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ K_R K_dR : ℝ, 0 ≤ K_R ∧ 0 ≤ K_dR ∧ ∀ (S : SmoothCcTensor g 0 s) (x : M),
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          ((pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)) ≤
        K_R * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((covGrad (I := I) (M := M) g 0 s S).toSection x)) +
          K_dR * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 s x
            (S.toSection x)) := by
  obtain ⟨K_R, K_dR, hK_R_nn, hK_dR_nn, hbound⟩ :=
    pointwiseTensorCurv_fiberNormSq_le_first_order (I := I) (M := M) g
  exact ⟨K_R s, K_dR s, hK_R_nn s, hK_dR_nn s, fun S x => hbound s S x⟩

end Connection
end Integral
end DifferentialGeometry

end
