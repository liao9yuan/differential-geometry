import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameRemainderFrameSumBridge

/-!
# The intrinsic frame-summed Weitzenböck bracket remainder fibre order

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file isolates the single
genuinely-irreducible **pointwise** quantitative content of the rank-generic order-`2` rough-Laplacian /
covariant-gradient commutator defect once the pure-Riemann channel is peeled off: the *intrinsic
frame-summed* moving-frame bracket remainder

```
∑ᵢ remDiffBracketFib g s S x i,   Bᵢ := smoothOrthoFrame g x i
```

is **order-`≤ 2`** in `S`, with a valence-dependent uniform fibre bound by the sum of the fibre norms of
`∇²S`, `∇S` and `S`. Here `remDiffBracketFib` (`MovingFrameRemainderFrameSumBridge`) is the named
moving-frame remainder `remDiffFib − remDiffGenuineFib` of the frame summand: the difference of the
per-direction third-order summand `remDiffFib g s S x i := ∇²_{Bᵢ, Bᵢ}(∇S)(x) − covGradBundleEquiv 0 s x
(∇·(∇²_{Bᵢ, Bᵢ} S)(x))` and its pure-Riemann genuine curvature fibre `remDiffGenuineFib` (the slot-`0`
uncurry of `v ↦ R(Bᵢ, v)(∇_{Bᵢ} S)`).

## Why this is the irreducible pointwise atom (frame-summed, not per-direction)

By the sorry-free frame-sum representation `pointwiseTensorCurv_toSection_eq_frame_sum`
(`Bochner/PointwiseTensorBochner`) the defect's section value is `∑ᵢ remDiffFib g s S x i`, each summand
splits as `remDiffFib = remDiffGenuineFib + remDiffBracketFib` (`remDiffFib_eq_genuine_add_bracket`), and
the pure-Riemann genuine fibres frame-sum to the concrete pure-Riemann section value
`∑ᵢ remDiffGenuineFib = (GcurvSection g s S).toSection x`
(`remDiffGenuineFib_sum_eq_GcurvSection_toSection`), so the frame-summed bracket remainder is exactly the
defect with the pure-Riemann trace removed,
`∑ᵢ remDiffBracketFib g s S x i = (pointwiseTensorCurv g s S − GcurvSection g s S).toSection x`.

The order is `≤ 2` only **after the frame sum**: each per-direction summand `remDiffFib g s S x i` is
genuinely `∇³S`-order — both `∇²_{Bᵢ, Bᵢ}(∇S)` and `∇(∇²_{Bᵢ, Bᵢ} S)` are individually third covariant
derivatives of `S` — and the top-order `∇³S` terms cancel only in the *trace* `∑ᵢ ∇²_{Bᵢ, Bᵢ}`, by the
rank-`(0, s + 1)` Ricci identity `secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen`
(`IntegratedOrder2WeitzenbockCurvature`). After the cancellation the surviving frame-summed remainder
carries the differentiated-curvature `(∇R) S` channel (`rfns(S)`-order) and the `∇²S`-order frame-bracket
discrepancy, with every curvature coefficient absorbed uniformly over the compact manifold (the `‖R‖_∞` /
`‖∇R‖_∞` `g`-norm sups `exists_uniform_riemannianFiberNormSq_riemannOp_bound`,
`exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound`). The `∇³S`-cancellation and the
`∇²S`-order bound are *false term-by-term* through the non-tensorial per-direction `smoothExtensionTangent`
reading (chart-selection-unbounded on `S²`); **only the intrinsic frame-summed remainder is `∇²S`-order**.

## Why this is homed here (the upstream cut)

The aggregate order-`2` commutator-defect fibre order (`exists_pointwiseTensorCurv_fiberOrder_bound`,
`Order2DefectFiberOrder`) and the four-carrier moving-frame remainder fibre bound
(`fourCarrierRemainder_fiberNormSq_bound_upstream`, `MovingFrameDiffCurvTraceSection`) both *consume* this
pointwise content; the latter additionally re-expresses it through the gauge-glued differentiated-curvature
carrier `genuineDiffCurvSection`, which is itself defined downstream in the moving-frame divergence spine.
Stating the remainder bound for the intrinsic frame sum `∑ᵢ remDiffBracketFib`, which depends only on the
sorry-free frame-sum bridge `MovingFrameRemainderFrameSumBridge`, homes it strictly *upstream* of that
spine, so the downstream consumers read it without an import cycle through the `L²` chain.

## Main result

* `exists_bracketThirdCurvField_frameSum_fiberNormSq_bound` — the **intrinsic frame-summed Weitzenböck
  bracket remainder fibre order**: a valence-dependent nonnegative constant `C : ℕ → ℝ` such that at every
  covariant rank `s`, every smooth compactly-supported `(0, s)`-tensor `S`, and *every point* `x`,
  ```
  rfns(∑ᵢ remDiffBracketFib g s S x i)(x) ≤ (C s)² · ( rfns(∇²S)(x) + rfns(∇S)(x) + rfns(S)(x) ).
  ```
  Stated for the intrinsic fibre norm `rfns` of the single frame-summed tensor throughout — never a
  per-direction `M → E` quantity — so it is trap-screened (T1-clean).

## Convention

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` (frame trace). All fibre norms are the intrinsic Riemannian
fibre norm `riemannianFiberNormSq` (`rfns`).
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

/-- **The intrinsic frame-summed Weitzenböck bracket remainder fibre order (posited genuine pointwise
leaf).** For a closed smooth Riemannian manifold `(M, g)` there is a *valence-dependent* nonnegative
constant `C : ℕ → ℝ` such that, at every covariant rank `s`, every smooth compactly-supported
`(0, s)`-tensor `S`, and *every point* `x`, the intrinsic fibre norm of the *frame-summed* moving-frame
bracket remainder `∑ᵢ remDiffBracketFib g s S x i` (`Bᵢ := smoothOrthoFrame g x i`) — the order-`2`
rough-Laplacian / covariant-gradient commutator defect with the pure-Riemann channel peeled off — is
bounded by `(C s)²` times the **sum** of the intrinsic fibre norms of `∇²S = covGrad g 0 (s + 1)
(covGrad g 0 s S)`, `∇S = covGrad g 0 s S` and `S`:
```
rfns(∑ᵢ remDiffBracketFib g s S x i)(x)
  ≤ (C s)² · ( rfns(∇²S)(x) + rfns(∇S)(x) + rfns(S)(x) ).
```

**Why this is TRUE — the iterated Ricci identity controls the frame-summed remainder.** The frame-summed
bracket remainder is exactly the defect with the pure-Riemann trace removed,
`∑ᵢ remDiffBracketFib g s S x i = (pointwiseTensorCurv g s S − GcurvSection g s S).toSection x` (the
sorry-free frame-sum identities `pointwiseTensorCurv_toSection_eq_frame_sum`,
`remDiffFib_eq_genuine_add_bracket`, `remDiffGenuineFib_sum_eq_GcurvSection_toSection`). Reading the rough
Laplacian as the `g`-metric trace `∑ᵢ ∇²_{Bᵢ, Bᵢ}` of the second covariant derivative and commuting the
new gradient slot past the two trace slots by the rank-`(0, s + 1)` Ricci identity
`secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen` (`IntegratedOrder2WeitzenbockCurvature`), the top-order
`∇³S` terms cancel *in the trace*: the difference is a sum of curvature contractions — the pure-Riemann
`R(∇S)` trace (already removed as `GcurvSection`, `rfns(∇S)`-order), the differentiated-curvature `(∇R) S`
contraction (`rfns(S)`-order) and the `∇²S`-order frame-bracket discrepancy — with every curvature
coefficient absorbed uniformly over the compact manifold (`exists_uniform_riemannianFiberNormSq_riemannOp_bound`,
`exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound`, the `‖R‖_∞` / `‖∇R‖_∞` `g`-norm sups). The
`∇³S`-cancellation and the `∇²S`-order bound are *false term-by-term* through the non-tensorial
per-direction `smoothExtensionTangent` reading (chart-selection-unbounded on `S²`, deleted as the false
chartJ route): each per-direction summand `remDiffFib g s S x i` is itself genuinely `∇³S`-order, and the
cancellation occurs only after the frame sum `∑ᵢ`. **Only the intrinsic frame-summed remainder is
`∇²S`-order.** The bound is stated for the intrinsic fibre norm `rfns` of the single frame-summed tensor
`∑ᵢ remDiffBracketFib g s S x i` throughout (never a per-direction `M → E` quantity), so it is
trap-screened (T1-clean).

**Why this is the upstream cut.** The pointwise frame-summed Bochner identity that would reduce this bound
to its concrete order-`≤ 2` curvature carriers is available only in *integrated* (`L²`-pairing) form
(`bracketRemainderFrameSum_integral_eq_diffCurvOpField_ricTrace`, `BracketDiscrepancyNullity`), and the
gauge-glued differentiated-curvature carrier `genuineDiffCurvSection` it would anchor on is defined
downstream in the moving-frame divergence spine; the downstream pointwise producers
(`exists_pointwiseTensorCurv_fiberOrder_bound`, `fourCarrierRemainder_fiberNormSq_bound_upstream`) all
transit this very content, so they cannot supply it without a cycle. This is therefore the precise
intrinsic frame-summed pointwise frontier of the curvature line, homed here above the moving-frame spine;
the body is `sorry` (the genuine classical pointwise third-order tensor Bochner–Weitzenböck curvature-term
derivation, frame-summed) and consumers transitively depend on its `sorryAx`.

**Non-vacuity (the `s = 0` litmus rejects `C ≡ 0`).** With `C s = 0` the bound would force
`rfns(∑ᵢ remDiffBracketFib g s S x i)(x) = 0`, i.e. `pointwiseTensorCurv g s S = GcurvSection g s S` at
every point. At `s = 0` the pure-Riemann trace `GcurvSection g 0 f` is the curvature of a scalar, so the
bound would force the scalar commutator defect `Curv f = Δ_∇(∇f) − ∇(Δ_∇ f)` to coincide with the
pure-Riemann trace pointwise — false on a non-flat manifold (`R ≠ 0`) for a non-harmonic `f`, since the
defect additionally carries the differentiated-curvature `(∇R) f` and the genuine Ricci-trace channels
(the integrated Weitzenböck identity `weitzenbock_integrated_covGrad_l2_normSq` gives the nonzero pairing
`⟨Curv f, ∇f⟩_{L²} = ‖Δ_∇ f‖²_{L²} − ‖∇²f‖²_{L²}`, nonzero when curvature is present, so the remainder is
not always zero). So `C` is genuinely positive, and the remainder genuinely uses `S`. -/
theorem exists_bracketThirdCurvField_frameSum_fiberNormSq_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            (∑ i : Fin (Module.finrank ℝ E),
              remDiffBracketFib (I := I) (M := M) g s S x i) ≤
          C s ^ 2 *
            (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
                ((covGrad (I := I) (M := M) g 0 (s + 1)
                  (covGrad (I := I) (M := M) g 0 s S)).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
                  ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x)) :=
  sorry

end Connection
end Integral
end DifferentialGeometry

end
