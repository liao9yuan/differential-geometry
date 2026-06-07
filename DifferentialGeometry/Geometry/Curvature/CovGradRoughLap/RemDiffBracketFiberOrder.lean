import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameRemainderFrameSumBridge

/-!
# The fibre order of the per-direction moving-frame remainder bracket summand

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file isolates the single
genuinely-irreducible quantitative fibre atom that survives once the pure-Riemann channel of the
order-`2` rough-Laplacian / covariant-gradient commutator defect `Curv S := Δ_∇(∇S) − ∇(Δ_∇ S)`
(`pointwiseTensorCurv g s S`, `∇S = covGrad g 0 s S`) has been peeled off: the **per-direction
frame-bracket remainder** `remDiffBracketFib g s S x i` (`MovingFrameRemainderFrameSumBridge`).

## Why this is the irreducible per-direction fibre atom

The defect's section value is the fixed-`g`-orthonormal-frame sum of the per-summand third-order
difference `remDiffFib g s S x i := ∇²_{Bᵢ, Bᵢ}(∇S)(x) − ∇·(∇²_{Bᵢ, Bᵢ} S)(x)`
(`pointwiseTensorCurv_toSection_eq_frame_sum`, `Bochner/PointwiseTensorBochner`). Each summand splits
into its pure-Riemann genuine curvature fibre `remDiffGenuineFib g s S x i` (the slot-`i` curvature
trace `v ↦ R(Bᵢ, v)(∇_{Bᵢ} S)`, genuinely tensorial, frame-summing to the concrete pure-Riemann
section `GcurvSection g s S`) and the named frame-bracket remainder
`remDiffBracketFib g s S x i := remDiffFib g s S x i − remDiffGenuineFib g s S x i`
(`remDiffFib_eq_genuine_add_bracket`).

The summand `remDiffFib` carries the top-order `∇³S` term `∇²_{Bᵢ, Bᵢ}(∇S)` (a second covariant
derivative of the gradient field, genuinely third-order in `S`), so `remDiffFib` *alone* is **not**
fibre-bounded by the order-`≤ 2` sum `rfns(∇²S) + rfns(∇S) + rfns(S)`. The point of the bracket
remainder is the cancellation: in `remDiffBracketFib = remDiffFib − remDiffGenuineFib` the top-order
`∇³S` in `∇²(∇S)` cancels against the `∇³S` hidden in `∇(∇²S)` through the iterated Ricci identity
`secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen` (`IntegratedOrder2WeitzenbockCurvature`), leaving a
curvature-contraction `R(∇S)` term (the residue past the tensorial pure-Riemann fibre), a
differentiated-curvature `(∇R) S` term, and a frame-bracket / frame-trace `∇²S`-order discrepancy. The
surviving remainder is therefore genuinely order-`≤ 2` in `S`. This is the genuine classical
moving-frame third-order curvature content; it has no sorry-free realisation upstream of the
moving-frame divergence spine, so it is posited here as the precise per-direction frontier.

## Main result

* `exists_remDiffBracketFib_fiberOrder_bound` — the **per-direction bracket-summand fibre order**: a
  *valence-dependent* nonnegative constant `C : ℕ → ℝ` such that at every covariant rank `s`, smooth
  compactly-supported `(0, s)`-tensor `S`, point `x`, and frame index `i`,
  ```
  rfns(remDiffBracketFib g s S x i)(x) ≤ (C s)² · ( rfns(∇²S)(x) + rfns(∇S)(x) + rfns(S)(x) ).
  ```
  Summing this over the finite `g_x`-orthonormal frame with the `n`-sub-additivity
  `riemannianFiberNormSq_sum_le_card_mul` (`FiberNormSubadditivity`) and identifying the bracket
  frame-sum with the moving-frame remainder `Curv S − GcurvSection g s S` via
  `pointwiseTensorCurv_toSection_eq_frame_sum`, `remDiffFib_eq_genuine_add_bracket`, and
  `remDiffGenuineFib_sum_eq_GcurvSection_toSection` is the upstream-safe reduction performed in
  `exists_pointwiseTensorCurv_subGcurv_obstruction_fiberOrder_bound` (`Order2DefectFiberOrder`).

## Convention

All fibre norms are the intrinsic Riemannian fibre norm `riemannianFiberNormSq` (`rfns`).
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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- **Posited per-direction moving-frame bracket-summand fibre order (the order-`2` commutator defect
with the pure-Riemann channel peeled off, per frame direction).** For a closed smooth Riemannian
manifold `(M, g)` there is a *valence-dependent* nonnegative constant `C : ℕ → ℝ` such that, at every
covariant rank `s`, every smooth compactly-supported `(0, s)`-tensor `S`, point `x`, and frame index
`i`, the intrinsic fibre norm of the per-direction frame-bracket remainder
`remDiffBracketFib g s S x i := remDiffFib g s S x i − remDiffGenuineFib g s S x i`
(`MovingFrameRemainderFrameSumBridge`) — the `i`-th summand of the order-`2` rough-Laplacian /
covariant-gradient commutator defect with its pure-Riemann curvature fibre subtracted off — is bounded
by `(C s)²` times the **sum** of the intrinsic fibre norms of `∇²S`, `∇S` and `S`:
```
rfns(remDiffBracketFib g s S x i)(x)
  ≤ (C s)² · ( rfns(∇²S)(x) + rfns(∇S)(x) + rfns(S)(x) ).
```

**This is the genuine, strictly-smaller, irreducible pointwise content of the curvature-defect fibre
order.** The summand `remDiffFib g s S x i = ∇²_{Bᵢ, Bᵢ}(∇S)(x) − ∇·(∇²_{Bᵢ, Bᵢ} S)(x)` carries the
top-order `∇³S` term `∇²_{Bᵢ, Bᵢ}(∇S)`, so it is **not** order-`≤ 2` by itself; the bracket remainder
is order-`≤ 2` precisely because the top-order `∇³S` cancels through the iterated Ricci identity
`secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen` (`IntegratedOrder2WeitzenbockCurvature`), leaving the
residual curvature-contraction `R(∇S)` term (the residue past the tensorial pure-Riemann fibre
`remDiffGenuineFib`, each fibre-bounded by `‖R‖_∞ · rfns(∇S)` via `riemannOp_covGrad_fiberNormSq_le_gen`),
the differentiated-curvature `(∇R) S` term (`rfns(S)`-order via the uniform `‖∇R‖_∞` bound
`exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound`), and the `∇²S`-order frame-bracket /
frame-trace discrepancy of the moving frame. Aggregating the three over the per-point curvature sup made
*uniform* over `M` by compactness gives the single nonnegative valence-dependent `C`.

**Why the bound is intrinsic and trap-screened.** The bound is stated for the intrinsic Riemannian fibre
norm `rfns` of the single tensor `remDiffBracketFib g s S x i` throughout — it never extracts a
per-direction `M → E` quantity, never reads a chart-selection-unbounded `smoothExtensionTangent` jet.
The `∇³S`-cancellation is *false term-by-term* through the non-tensorial reading (chart-selection-unbounded
on `S²`); only the intrinsic frame-summand difference is `∇²S`-order.

**Non-vacuity (the `s = 0` litmus).** With `C s = 0` the bound forces
`rfns(remDiffBracketFib g s S x i)(x) = 0` for every direction `i`, hence
`remDiffBracketFib g s S x i = 0` for every `i`, hence the frame sum
`∑ᵢ remDiffBracketFib g s S x i = 0`. But that frame sum is exactly the moving-frame remainder
`(Curv S − GcurvSection g s S).toSection x` of the order-`2` commutator defect
(`pointwiseTensorCurv_toSection_eq_frame_sum` minus `remDiffGenuineFib_sum_eq_GcurvSection_toSection`),
which is *nonzero* on a non-flat manifold (`R ≠ 0`) for a non-parallel `S`: it carries the
differentiated-curvature `(∇R) S` channel together with the moving-frame bracket discrepancy
(`⟨Curv S, ∇S⟩_{L²} = ‖Δ_∇ S‖²_{L²} − ‖∇²S‖²_{L²}`, `weitzenbock_integrated_covGrad_l2_normSq`, nonzero
when curvature is present). At `s = 0` already the scalar commutator defect `Curv f = Ric(∇f, ·)`
integrated is nonzero for a non-harmonic `f` on a curved manifold. So `C` is genuinely positive, and the
summand `remDiffBracketFib` genuinely uses `S` (through the `∇²(∇S)` term of `remDiffFib`). The body is
`sorry` (the genuine classical moving-frame third-order curvature content: the `∇³S` cancellation through
the iterated Ricci identity, followed by the differentiated-curvature and bracket-discrepancy fibre
sups); consumers transitively depend on `sorryAx`. -/
theorem exists_remDiffBracketFib_fiberOrder_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) (i : Fin (Module.finrank ℝ E)),
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            (remDiffBracketFib (I := I) (M := M) g s S x i) ≤
          C s ^ 2 *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
                ((covGrad (I := I) (M := M) g 0 (s + 1)
                  (covGrad (I := I) (M := M) g 0 s S)).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                  ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x)) := by
  sorry

end Connection
end Integral
end DifferentialGeometry

end
